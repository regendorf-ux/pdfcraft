#!/usr/bin/env python3
"""Keep a contributor's open pull requests mergeable while the base branch moves.

Every upstream change to a translation catalog changes the SHA-256 pinned for it in
ATTRIBUTION.toml, so each open pull request that also edits that file (or holds an older copy)
shows a conflict after almost every upstream commit. This script merges the base branch into each
open pull request branch and resolves the conflicts it knows how to resolve safely. Two levels:

level "pins" (the scheduled default; the mechanical kinds only):
  * translation catalogs (crates/ui-egui/src/i18n/*.tsv), ROADMAP.md and docs/gaps.md: both
    sides' lines are kept (git's union merge); the catalogs are then checked for rows with the
    wrong number of columns and for the same key translated twice;
  * ATTRIBUTION.toml / ATTRIBUTION.md: the base branch's copy, with every [[asset]] sha256
    recomputed from the file it names;
  * Cargo.lock: the base branch's copy, re-resolved for the workspace only;
  * anything else that conflicts: the merge is abandoned and the branch is listed for a person.

level "all" (everything above, plus):
  1. a catalog key (context, source) with a row on both sides: merged three-way by key: the
     pull request's own additions and changes are kept; where both sides wrote the same key
     differently, the base branch's row wins (the summary names each one);
  2. parity/acrobat-features.toml: merged by feature id, the base branch's file as the base and
     the pull request's added and changed features on top; a feature both sides changed, or one
     changed on one side and removed on the other, leaves the branch for a person, with the id;
  3. code and other text files: an earlier recorded resolution (git rerere, trained from the
     merges people made on these branches), else a syntax-aware merge (mergiraf), else an
     additions-only union (both sides only added lines at the same place: the base branch's
     lines first, then the pull request's). Every resolved file must pass the hazard checks (no
     conflict markers; for Rust, the brace balance of a parent and every test function of both
     parents still marked as a test). A branch where any Rust-side file was resolved this way
     must then pass, in the same run, rustfmt, clippy over the whole workspace (any error fails;
     warnings fail in the crates it touched) and the tests of the crates it touched; otherwise
     it is left for a person, untouched, with the reason.

Each branch's work is planned first, and only what it needs runs: a catalog-only merge costs a
lint and a hash pass, Cargo.lock adds `cargo update -w`, the parity file adds its TOML check, and
cargo builds run only for a branch whose code a resolver changed. The workflow uses the plan to
install mergiraf and the Rust toolchain only when some branch needs them.

It only ever adds a plain merge commit on top of a branch (no rebase, no force push; a push that
is not a fast-forward is refused by git), and it leaves a branch alone when it already contains
the base branch. Dry run by default: it merges in a scratch worktree, reports what it would push,
and pushes nothing unless PUSH=1.

Commands (default: run = classify, resolve, verify, finish in one process):
  classify   which branches need work, and of which kinds (no worktree; sets the setup flags)
  resolve    merge and resolve each branch, commit to refs/keeper/<branch> (no cargo builds)
  verify     the cargo checks for the branches that need them
  finish     push (PUSH=1) and write the report
  replay SHA...   re-run the resolvers on each merge commit's two parents and compare the result
                  with what was committed (never pushes)

Environment:
  UPSTREAM_REPO     owner/name of the repository the pull requests are open on (storytold/pdfcraft)
  PR_AUTHOR         only pull requests by this login
  UPSTREAM_REMOTE   git remote of the base repository (default: upstream)
  FORK_REMOTE       git remote holding the pull request branches (default: origin)
  BASE              base branch (default: main)
  LEVEL             pins (default) or all
  ONLY              comma-separated branch names to handle (default: all open pull requests)
  PUSH              1 to push the merge commits (default: dry run)
  REPLAY            comma-separated merge commits: rehearse on them instead of the open branches
  KEEPER_STATE      the state file shared by the commands (default: in the system temp folder)
  KEEPER_WORK       the scratch worktree (default: in the system temp folder)
"""
from __future__ import annotations

import collections
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager
from pathlib import Path

UPSTREAM_REPO = os.environ.get("UPSTREAM_REPO", "storytold/pdfcraft")
UPSTREAM_REMOTE = os.environ.get("UPSTREAM_REMOTE", "upstream")
FORK_REMOTE = os.environ.get("FORK_REMOTE", "origin")
BASE = os.environ.get("BASE", "main")
PUSH = os.environ.get("PUSH", "") == "1"
LEVEL = os.environ.get("LEVEL", "pins").strip() or "pins"
ONLY = {b.strip() for b in os.environ.get("ONLY", "").split(",") if b.strip()}
REPLAY = [s.strip() for s in os.environ.get("REPLAY", "").split(",") if s.strip()]
_TMP = Path(os.environ.get("RUNNER_TEMP") or tempfile.gettempdir())
STATE = Path(os.environ.get("KEEPER_STATE") or _TMP / "keep-prs-state.json").resolve()
WORK = Path(os.environ.get("KEEPER_WORK") or _TMP / "keep-prs-work").resolve()
TARGET = Path(os.environ.get("CARGO_TARGET_DIR") or _TMP / "keep-prs-target").resolve()
# KEEPER_CARGO=0 leaves the cargo checks out (a local replay of the resolvers only).
CARGO_CHECKS = os.environ.get("KEEPER_CARGO", "1") != "0"
# A big crate (more integration test programs than this) gets its library tests, its grouped
# test programs and the programs whose files were resolved, not all of them: each links the
# whole stack.
TEST_TARGET_LIMIT = int(os.environ.get("KEEPER_TEST_TARGET_LIMIT", "8"))
GROUPED_TESTS = ("ui_group", "it")
if LEVEL not in ("pins", "all"):
    sys.exit(f"LEVEL must be pins or all, not {LEVEL!r}")


def _skip_list() -> set:
    """Branches left alone: SKIP (comma-separated) and the lines of SKIP_FILE (# starts a comment)."""
    names = {b.strip() for b in os.environ.get("SKIP", "").split(",") if b.strip()}
    path = Path(os.environ.get("SKIP_FILE", ".github/keep-prs-current/skip.txt"))
    if path.exists():
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.split("#", 1)[0].strip()
            if line:
                names.add(line)
    return names


SKIP = _skip_list()
CATALOGS = "crates/ui-egui/src/i18n/"
CATALOG = re.compile(r"^crates/ui-egui/src/i18n/[^/]+\.tsv$")
PARITY = "parity/acrobat-features.toml"
UNION_PATHS = (CATALOGS + "*.tsv", "ROADMAP.md", "docs/gaps.md")
MECHANICAL = re.compile(r"^(crates/ui-egui/src/i18n/[^/]+\.tsv|ATTRIBUTION\.toml|ATTRIBUTION\.md|ROADMAP\.md|docs/gaps\.md|Cargo\.lock)$")
# Files whose resolution needs the cargo checks: Rust sources and manifests, anything in a crate.
RUST_SIDE = re.compile(r"(\.rs$|(^|/)Cargo\.toml$|^(crates|apps|xtask|vendor)/)")
# Commits on a pull request branch carry the contributor's own identity (the repository owner's
# GitHub noreply address), as every other commit on these branches does.
_NAME = os.environ.get("KEEPER_NAME", "Osvaldo Duran")
_EMAIL = os.environ.get("KEEPER_EMAIL", "338149330+regendorf-ux@users.noreply.github.com")
for _k, _v in (("GIT_AUTHOR_NAME", _NAME), ("GIT_AUTHOR_EMAIL", _EMAIL), ("GIT_COMMITTER_NAME", _NAME), ("GIT_COMMITTER_EMAIL", _EMAIL)):
    os.environ[_k] = _v
TRAILER = "\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"


# ---------------------------------------------------------------- small helpers
def run(*args: str, cwd: Path | None = None, check: bool = True, inp: str | None = None, env: dict | None = None) -> str:
    r = subprocess.run(args, cwd=cwd, capture_output=True, text=True, input=inp, env=env)
    if check and r.returncode:
        raise RuntimeError(f"{' '.join(args)}: {r.stderr.strip() or r.stdout.strip()}")
    return r.stdout.strip()


def git(*args: str, cwd: Path | None = None, check: bool = True) -> str:
    return run("git", *args, cwd=cwd, check=check)


def show(rev: str, path: str, cwd: Path | None = None) -> str | None:
    """A file's text at a revision (None when it is absent or not UTF-8)."""
    r = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=cwd, capture_output=True)
    if r.returncode:
        return None
    try:
        return r.stdout.decode("utf-8")
    except UnicodeDecodeError:
        return None


def say(text: str) -> None:
    print(text, flush=True)


def output(**kw) -> None:
    """Step outputs for the workflow (no-op outside GitHub Actions)."""
    path = os.environ.get("GITHUB_OUTPUT")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            for k, v in kw.items():
                f.write(f"{k}={v}\n")


def load_state() -> dict:
    return json.loads(STATE.read_text(encoding="utf-8")) if STATE.is_file() else {}


def save_state(state: dict) -> None:
    STATE.write_text(json.dumps(state, indent=1), encoding="utf-8")


def common_dir() -> Path:
    d = Path(git("rev-parse", "--git-common-dir"))
    return d if d.is_absolute() else Path.cwd() / d


@contextmanager
def union_attributes():
    """The union merge rule for the catalogs and the two notes files, in the repository's own
    info/attributes (never committed), removed again afterwards."""
    attrs = common_dir() / "info" / "attributes"
    attrs.parent.mkdir(parents=True, exist_ok=True)
    old = attrs.read_text(encoding="utf-8") if attrs.exists() else None
    attrs.write_text((old or "") + "".join(f"{p} merge=union\n" for p in UNION_PATHS), encoding="utf-8")
    try:
        yield
    finally:
        if old is None:
            attrs.unlink(missing_ok=True)
        else:
            attrs.write_text(old, encoding="utf-8")


def merge_config(level: str) -> list:
    """git -c options for the merge itself (a replay never uses recorded resolutions, so it
    shows what the resolvers alone do)."""
    if level == "pins":
        return ["-c", "rerere.enabled=false"]
    rerere = "false" if REPLAY and not os.environ.get("KEEPER_REPLAY_RERERE") else "true"
    return ["-c", f"rerere.enabled={rerere}", "-c", "rerere.autoUpdate=false", "-c", "merge.conflictStyle=zdiff3"]


def merge_strategy(level: str) -> list:
    return ["-X", "diff-algorithm=histogram"] if level == "all" else []


# ---------------------------------------------------------------- catalogs
def lint_catalog(path: Path, already: set = frozenset()) -> list:
    """Problems in one catalog: rows without 3 columns, and a key translated twice (except the
    keys in `already`, which a parent branch itself has twice)."""
    problems, seen = [], {}
    for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        cols = line.split("\t")
        if len(cols) != 3:
            problems.append(f"{path.name}:{n}: {len(cols)} columns, not 3")
            continue
        key = (cols[0], cols[1])
        if key in seen and seen[key] != line and key not in already:
            problems.append(f"{path.name}:{n}: {cols[1][:40]!r} translated twice")
        seen.setdefault(key, line)
    return problems


def drop_exact_duplicate_rows(path: Path) -> bool:
    """The union merge can leave the same row twice; drop the second copy."""
    out, seen, changed = [], set(), False
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip() and not line.startswith("#"):
            if line in seen:
                changed = True
                continue
            seen.add(line)
        out.append(line)
    if changed:
        path.write_text("\n".join(out) + "\n", encoding="utf-8")
    return changed


def catalog_rows(text: str | None) -> dict:
    """(context, source) -> row, for the rows of a catalog (the first of a repeated key)."""
    rows = {}
    for line in (text or "").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        cols = line.split("\t")
        if len(cols) == 3:
            rows.setdefault((cols[0], cols[1]), line)
    return rows


def repeated_keys(*texts: str | None) -> set:
    """The keys some of these catalogs already translate twice (left as they are)."""
    out = set()
    for text in texts:
        rows = collections.defaultdict(set)
        for line in (text or "").splitlines():
            cols = line.split("\t")
            if line.strip() and not line.startswith("#") and len(cols) == 3:
                rows[(cols[0], cols[1])].add(line)
        out |= {k for k, v in rows.items() if len(v) > 1}
    return out


def union_three_way(base: str | None, ours: str | None, theirs: str | None) -> str | None:
    """Both sides' lines in the order git's union merge gives them (the pull request's, then
    upstream's lines it lacks), but a line one side removed and the other left alone stays
    removed, which the union merge does not do. None when git cannot merge the file."""
    with tempfile.TemporaryDirectory(prefix="keep-prs-") as d:
        paths = []
        for name, text in (("ours", ours), ("base", base), ("theirs", theirs)):
            p = Path(d) / name
            p.write_text(text or "", encoding="utf-8")
            paths.append(str(p))
        r = subprocess.run(["git", "merge-file", "-p", "--diff3", *paths], capture_output=True, text=True)
    if r.returncode < 0 or r.returncode > 127:
        return None
    out, cur = [], None
    for line in r.stdout.splitlines(keepends=True):
        m = MARK.match(line)
        if m and m.group(1) == "<<<<<<<":
            cur = {"ours": [], "base": [], "theirs": [], "part": "ours"}
        elif cur and m and m.group(1) == "|||||||":
            cur["part"] = "base"
        elif cur and m and m.group(1) == "=======":
            cur["part"] = "theirs"
        elif cur and m and m.group(1) == ">>>>>>>":
            o, b, t = cur["ours"], cur["base"], cur["theirs"]
            gone_o = {l for l in b if l not in o and l.strip()}    # the pull request removed it
            gone_t = {l for l in b if l not in t and l.strip()}    # upstream removed it
            out += [l for l in o if l not in gone_t]
            out += [l for l in t if l not in gone_o and (not l.strip() or l not in o)]
            cur = None
        elif cur:
            cur[cur["part"]].append(line)
        else:
            out.append(line)
    return "".join(out)


def merge_catalog_by_key(merged: str, base: str | None, ours: str | None, theirs: str | None) -> tuple:
    """Item 1: the union merge's text, with every key three-way merged: a side's change wins
    where the other side left the row as it was, a row one side removed (and the other left
    alone) goes, the same row twice stays once, and where both sides wrote the key differently
    the base branch's row wins. Order and comment lines are the union merge's. (text, notes)"""
    b, o, t = catalog_rows(base), catalog_rows(ours), catalog_rows(theirs)
    notes, want = [], {}
    keep = repeated_keys(ours, theirs)                 # a parent's own repeated key: not ours to fix
    for key in (set(o) | set(t) | set(b)) - keep:
        bo, oo, to = b.get(key), o.get(key), t.get(key)
        if oo == to:
            row = oo
        elif oo == bo:
            row = to                                   # only the base branch changed (or removed) it
        elif to == bo:
            row = oo                                   # only the pull request changed (or removed) it
        else:
            row = to if to is not None else oo         # both: the base branch's row wins
            if to is not None and oo is not None:
                notes.append(key[1][:50])
        want[key] = row
    out, done = [], set()
    for line in merged.splitlines():
        cols = line.split("\t")
        if not line.strip() or line.startswith("#") or len(cols) != 3:
            out.append(line)
            continue
        key = (cols[0], cols[1])
        if key in keep:
            if line not in out:
                out.append(line)
            continue
        if key in done:
            continue
        done.add(key)
        if key not in want:
            out.append(line)                           # a row the three sides do not explain: kept
        elif want[key] is not None:
            out.append(want[key])
    for key, row in want.items():                      # a row the union lost (should not happen)
        if row is not None and key not in done:
            out.append(row)
    return "\n".join(out) + ("\n" if merged.endswith("\n") or not merged else ""), notes


# ---------------------------------------------------------------- ATTRIBUTION
def attribution_hashes(root: Path, recompute: bool) -> list:
    """Recompute (or only verify) every [[asset]] sha256 in ATTRIBUTION.toml; the mismatches left."""
    path = root / "ATTRIBUTION.toml"
    if not path.exists():
        return []
    s = path.read_text(encoding="utf-8")
    pat = re.compile(r'(path = "([^"]+)"(?:\n(?!\[\[asset\]\]).*)*?\nsha256 = ")([0-9a-f]{64})(")')
    bad = []

    def fix(m):
        rel, old = m.group(2), m.group(3)
        try:
            h = hashlib.sha256((root / rel).read_bytes()).hexdigest()
        except FileNotFoundError:
            return m.group(0)
        if h == old:
            return m.group(0)
        if recompute:
            return m.group(1) + h + m.group(4)
        bad.append(rel)
        return m.group(0)

    s2 = pat.sub(fix, s)
    if recompute and s2 != s:
        path.write_text(s2, encoding="utf-8")
    return bad


def unpinned_changes(base: str | None, ours: str | None) -> bool:
    """Did the pull request change ATTRIBUTION.toml in more than its sha256 lines?"""
    strip = lambda t: re.sub(r'(?m)^sha256 = "[0-9a-f]{64}"$', "", t or "")
    return strip(base) != strip(ours)


# ---------------------------------------------------------------- the parity file (item 2)
def feature_blocks(text: str) -> tuple:
    """The parity file as (header, [(id, gap, body)]): `gap` is the comment and blank lines
    before a [[feature]] table, `body` the table itself."""
    parts = re.split(r"(?m)^(?=\[\[feature\]\])", text)
    head, items, seen = parts[0], [], collections.Counter()
    gap = ""
    lines_head = head.splitlines(keepends=True)
    # The comment/blank lines at the end of the header belong to the first feature.
    while lines_head and (not lines_head[-1].strip() or lines_head[-1].lstrip().startswith("#")) and len(lines_head) > 1:
        gap = lines_head.pop() + gap
    head = "".join(lines_head)
    for p in parts[1:]:
        lines = p.splitlines(keepends=True)
        tail = ""
        while lines and (not lines[-1].strip() or lines[-1].lstrip().startswith("#")):
            tail = lines.pop() + tail
        body = "".join(lines)
        m = re.search(r'(?m)^id\s*=\s*"([^"]+)"', body)
        key = m.group(1) if m else body.splitlines()[0]
        seen[key] += 1
        items.append((key if seen[key] == 1 else f"{key}#{seen[key]}", gap, body))
        gap = tail
    return head, items, gap


def merge_parity(base: str, ours: str, theirs: str) -> tuple:
    """(text or None, notes, problems): the base branch's file with the pull request's added,
    changed and removed features on top; any feature both sides touched differently is a
    problem (the branch is left for a person)."""
    hb, b, _ = feature_blocks(base)
    ho, o, _ = feature_blocks(ours)
    ht, t, tail = feature_blocks(theirs)
    bd, od, td = ({k: body for k, _, body in x} for x in (b, o, t))
    problems, notes = [], []
    head = ho if (ho != hb and ht == hb) else ht
    if ho != hb and ht != hb and ho != ht:
        problems.append(f"{PARITY}: the header changed on both sides")
    result = [[k, g, body] for k, g, body in t]
    keys = [k for k, _, _ in result]
    added = changed = removed = 0
    for i, (k, g, body) in enumerate(o):
        if k not in bd:
            if k in td:
                if td[k] != body:
                    problems.append(f"{PARITY}: {k} added by both sides, differently")
                continue
            prev = next((o[j][0] for j in range(i - 1, -1, -1) if o[j][0] in keys), None)
            at = keys.index(prev) + 1 if prev is not None else len(result)
            result.insert(at, [k, g, body])
            keys.insert(at, k)
            added += 1
        elif body != bd[k]:
            if k not in td:
                problems.append(f"{PARITY}: {k} changed by the pull request but removed upstream")
            elif td[k] != bd[k] and td[k] != body:
                problems.append(f"{PARITY}: {k} changed by both sides")
            else:
                result[keys.index(k)][2] = body
                changed += 1
    for k in bd:
        if k not in od and k in td:
            if td[k] == bd[k]:
                idx = keys.index(k)
                # The removed feature's gap (a section banner) stays with the next one.
                if idx + 1 < len(result):
                    result[idx + 1][1] = result[idx][1] + result[idx + 1][1] if result[idx][1].strip() else result[idx + 1][1]
                del result[idx], keys[idx]
                removed += 1
            else:
                problems.append(f"{PARITY}: {k} removed by the pull request but changed upstream")
    if problems:
        return None, notes, problems
    text = head + "".join(g + body for _, g, body in result) + tail
    notes.append(f"{PARITY}: by feature id, upstream's file + the pull request's {added} added, {changed} changed, {removed} removed")
    return text, notes, []


def parity_facts(text: str | None) -> tuple:
    """(the TOML error or "", the feature ids there twice) of a parity file."""
    try:
        import tomllib
    except ImportError:                                # Python before 3.11: the id check only
        tomllib = None
    err = ""
    if tomllib is not None and text is not None:
        try:
            tomllib.loads(text)
        except Exception as e:                         # noqa: BLE001 - any parse error is the answer
            err = str(e)[:80]
    ids = re.findall(r'(?m)^id\s*=\s*"([^"]+)"', text or "")
    return err, {k for k, n in collections.Counter(ids).items() if n > 1}


def check_parity(path: Path, ours: str | None, theirs: str | None) -> list:
    """The merged parity file parses as TOML when both parents do, and repeats no feature id
    that neither parent repeats (upstream's own file has been invalid for a while before)."""
    err, twice = parity_facts(path.read_text(encoding="utf-8"))
    (oe, ot), (te, tt) = parity_facts(ours), parity_facts(theirs)
    out = []
    if err and not oe and not te:
        out.append(f"{PARITY}: not valid TOML ({err})")
    new = sorted(twice - ot - tt)
    if new:
        out.append(f"{PARITY}: feature id twice: {', '.join(new[:5])}")
    return out


# ---------------------------------------------------------------- code (item 3)
MARK = re.compile(r"^(<{7}|\|{7}|={7}|>{7})(?: |$)")


def conflict_hunks(text: str) -> list:
    """The zdiff3 conflict hunks of a file: ours, base (None without a base section), theirs."""
    hunks, cur, part = [], None, None
    for line in text.splitlines():
        m = MARK.match(line)
        if m and m.group(1) == "<<<<<<<":
            cur, part = {"ours": [], "base": None, "theirs": []}, "ours"
        elif m and m.group(1) == "|||||||" and cur:
            cur["base"], part = [], "base"
        elif m and m.group(1) == "=======" and cur:
            part = "theirs"
        elif m and m.group(1) == ">>>>>>>" and cur:
            hunks.append(cur)
            cur, part = None, None
        elif cur is not None:
            cur[part].append(line)
    return hunks


def has_markers(text: str) -> bool:
    return any((m := MARK.match(line)) and m.group(1) in ("<<<<<<<", ">>>>>>>", "|||||||") for line in text.splitlines())


def mergiraf_solve(path: Path) -> bool:
    """mergiraf on a conflicted file; True when it solved the whole file (else left as it was)."""
    if not shutil.which("mergiraf"):
        return False
    before = path.read_text(encoding="utf-8", errors="replace")
    r = subprocess.run(["mergiraf", "solve", "--keep-backup=false", str(path)], capture_output=True, text=True)
    if r.returncode == 0 and not has_markers(path.read_text(encoding="utf-8", errors="replace")):
        return True
    path.write_text(before, encoding="utf-8")
    return False


def brace_depth(lines) -> int:
    """Opening minus closing braces, outside strings, chars and // comments (a rough count)."""
    depth = 0
    for line in lines:
        code = re.sub(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\'|//.*', "", line)
        depth += code.count("{") - code.count("}")
    return depth


def union_additions(path: Path, rust: bool) -> bool:
    """Both sides only added lines where the base had none: the base branch's lines, then the
    pull request's. Every hunk must be such an addition (else nothing changes, False)."""
    text = path.read_text(encoding="utf-8", errors="replace")
    hunks = conflict_hunks(text)
    if not hunks or any(h["base"] is None or h["base"] for h in hunks):
        return False
    lines = text.splitlines(keepends=True)
    out, cur = [], None
    for j, line in enumerate(lines):
        m = MARK.match(line)
        if m and m.group(1) == "<<<<<<<":
            cur = {"ours": [], "theirs": [], "part": "ours"}
        elif cur and m and m.group(1) == "|||||||":
            cur["part"] = "base"
        elif cur and m and m.group(1) == "=======":
            cur["part"] = "theirs"
        elif cur and m and m.group(1) == ">>>>>>>":
            out += cur["theirs"]
            # Both sides appended an item (a test, an arm) after the base's last one and git kept
            # their common closing lines after the hunk: each side opens d braces more than it
            # closes, so upstream's item gets those d closing lines too, and the pull request's
            # item gets again the lines git lifted out of the hunk before it (`#[test]`, a shared
            # doc line).
            d = brace_depth(cur["theirs"]) if rust else 0
            after = lines[j + 1 : j + 1 + d]
            if d >= 1 and brace_depth(cur["ours"]) == d and len(after) == d and all(
                    re.fullmatch(r"\s*[}\])]+[;,]?\s*", x) for x in after):
                lead = []
                for prev in reversed(out[: len(out) - len(cur["theirs"])]):
                    if not prev.strip().startswith(("#[", "///")):
                        break
                    lead.insert(0, prev)
                out += after + ["\n"] + lead
            out += cur["ours"]
            cur = None
        elif cur:
            if cur["part"] in ("ours", "theirs"):
                cur[cur["part"]].append(line)
        else:
            out.append(line)
    path.write_text("".join(out), encoding="utf-8")
    return True


TEST_ATTR = re.compile(r"^\s*#\[(?:[\w:]+::)?test\b|^\s*#\[(?:tokio|async_std|rstest|test_case)\b")
FN = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?(?:const\s+)?(?:unsafe\s+)?fn\s+(\w+)")


def test_functions(text: str | None) -> tuple:
    """(names marked as tests, Counter of every fn name) in a Rust file."""
    tests, fns = collections.Counter(), collections.Counter()
    attrs = False
    for line in (text or "").splitlines():
        s = line.strip()
        if TEST_ATTR.match(line):
            attrs = True
            continue
        m = FN.match(line)
        if m:
            fns[m.group(1)] += 1
            if attrs:
                tests[m.group(1)] += 1
            attrs = False
        elif s and not s.startswith(("#[", "//", "///")):
            attrs = False
    return tests, fns


def hazards(rel: str, text: str, base: str | None, ours: str | None, theirs: str | None) -> list:
    """What makes a resolved file unsafe to take: conflict markers; in Rust, a brace balance
    that neither parent has, or a test of either parent that is gone or no longer a test."""
    out = []
    if has_markers(text):
        out.append(f"{rel}: conflict markers left")
    if not rel.endswith(".rs"):
        return out
    uses = lambda x: collections.Counter(m.group(1) for m in re.finditer(r"(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?use\s+([\w:]+)::\{", x or ""))
    ru, ou, tu = uses(text), uses(ours), uses(theirs)
    for path_, n in ru.items():
        if n > max(ou.get(path_, 0), tu.get(path_, 0)):
            out.append(f"{rel}: `use {path_}::{{…}}` is there {n} times")
    depth = brace_depth(text.splitlines())
    parents = {brace_depth((x or "").splitlines()) for x in (ours, theirs) if x is not None}
    if parents and depth not in parents:
        out.append(f"{rel}: braces do not balance as in either parent ({depth:+d})")
    rt, rf = test_functions(text)
    bt, _ = test_functions(base)
    for side, src, other in (("the pull request's", ours, theirs), ("upstream's", theirs, ours)):
        st, _ = test_functions(src)
        ot, _ = test_functions(other)
        for name, n in st.items():
            if bt.get(name, 0) and not ot.get(name, 0):
                continue                               # the other side removed it on purpose
            if rt.get(name, 0) < n:
                if rf.get(name, 0) > rt.get(name, 0):
                    out.append(f"{rel}: {side} test {name} lost its #[test]")
                else:
                    out.append(f"{rel}: {side} test {name} is gone")
    return out


# ---------------------------------------------------------------- one merge
def resolved_text(work: Path, rel: str) -> str:
    return (work / rel).read_text(encoding="utf-8", errors="replace")


def stages(work: Path, rel: str) -> tuple:
    """The base, ours and theirs texts of a conflicted file (None for a missing stage)."""
    return tuple(show(f":{n}", rel, cwd=work) for n in (1, 2, 3))


def merge_one(ours: str, theirs: str, label: str, level: str, work: Path) -> dict:
    """Merge `theirs` into `ours` in `work` and resolve what the level allows. On success the
    merge is committed (detached HEAD) and the result has status "merged" and the commit;
    otherwise the merge is aborted and the result says why ("by hand")."""
    t0 = time.time()
    res = {"status": "", "detail": "", "files": {}, "notes": [], "rust": [], "commit": "", "needs_cargo": False}
    git("checkout", "-q", "-f", "--detach", ours, cwd=work)
    r = subprocess.run(["git", *merge_config(level), "merge", "--no-ff", "--no-commit", "-q", *merge_strategy(level), theirs],
                       cwd=work, capture_output=True, text=True)
    conflicted = [f for f in git("diff", "--name-only", "--diff-filter=U", cwd=work).splitlines() if f]
    rerered = set(re.findall(r"Resolved '([^']+)' using previous resolution", r.stdout + r.stderr))
    res["timings"] = {"merge": round(time.time() - t0, 1)}

    def abort(detail: str) -> dict:
        git("merge", "--abort", cwd=work, check=False)
        git("reset", "-q", "--hard", cwd=work, check=False)
        res.update(status="by hand", detail=detail)
        return res

    if r.returncode and not conflicted:
        return abort((r.stderr or r.stdout).strip()[:200])
    if level == "pins":
        by_hand = [f for f in conflicted if not MECHANICAL.match(f)]
        if by_hand:
            return abort(", ".join(by_hand))
    base_rev = git("merge-base", ours, theirs, cwd=work, check=False).split("\n")[0] or None
    left, problems = [], []
    t1 = time.time()
    for f in conflicted:
        b, o, t = stages(work, f)
        if o is None or t is None:
            left.append(f"{f} (deleted on one side)")
            continue
        if f in ("ATTRIBUTION.toml", "ATTRIBUTION.md", "Cargo.lock"):
            if level == "all" and f.startswith("ATTRIBUTION") and (unpinned_changes(b, o) if f.endswith(".toml") else b != o):
                left.append(f"{f} (the pull request changes its entries; upstream's copy would drop them)")
                continue
            git("checkout", "--theirs", "--", f, cwd=work)
            res["files"][f] = "upstream's copy" + (", hashes recomputed" if f == "ATTRIBUTION.toml" else "")
            continue
        if MECHANICAL.match(f):                        # a catalog or notes file git could not union
            left.append(f"{f} (could not be merged line by line)")
            continue
        if f == PARITY:
            text, notes, probs = merge_parity(b or "", o, t)
            if text is None:
                left.append(f"{f} ({'; '.join(p.split(': ', 1)[1] for p in probs[:3])})")
                continue
            (work / f).write_text(text, encoding="utf-8")
            res["files"][f] = "by feature id"
            res["notes"] += notes
            continue
        # Code and other text: rerere, mergiraf, the additions-only union.
        path = work / f
        rust = bool(RUST_SIDE.search(f))
        how = None
        if f in rerered and not has_markers(resolved_text(work, f)):
            how = "an earlier resolution (rerere)"
        elif mergiraf_solve(path):
            how = "syntax-aware merge (mergiraf)"
        elif union_additions(path, f.endswith(".rs")):
            how = "additions from both sides, upstream's first"
        if how is None:
            n = len(conflict_hunks(resolved_text(work, f)))
            left.append(f"{f} ({n} hunk{'s' if n != 1 else ''} change the same lines)")
            continue
        found = hazards(f, resolved_text(work, f), b, o, t)
        if found:
            left.append(f"{f} ({how}, refused: {'; '.join(x.split(': ', 1)[1] for x in found[:2])})")
            continue
        res["files"][f] = how
        if rust:
            res["rust"].append(f)
    if left:
        return abort("; ".join(left))
    if "Cargo.lock" in conflicted or any(f.endswith("Cargo.toml") for f in res["rust"]):
        u = subprocess.run(["cargo", "update", "-w", "-q"], cwd=work, capture_output=True, text=True)
        if u.returncode and level == "all":
            return abort(f"cargo update -w: {(u.stderr or u.stdout).strip()[:160]}")
    # Every catalog the merge changed: the duplicate check (pins) or the merge by key (all).
    merged = set(git("diff", "--name-only", "HEAD", cwd=work).splitlines()) | set(conflicted)
    if level == "all" and base_rev:
        for f in sorted(merged):
            if (CATALOG.match(f) or f in ("ROADMAP.md", "docs/gaps.md")) and (work / f).exists():
                b, o, t = (show(r, f, cwd=work) for r in (base_rev, ours, theirs))
                if b is not None and o is not None and t is not None and o != b and t != b:
                    text = union_three_way(b, o, t)
                    if text is not None:
                        (work / f).write_text(text, encoding="utf-8")
    for f in sorted(merged):
        if not (CATALOG.match(f) and (work / f).exists()):
            continue
        if level == "all":
            text = (work / f).read_text(encoding="utf-8")
            fixed, both = merge_catalog_by_key(text, show(base_rev, f, cwd=work) if base_rev else None,
                                              show(ours, f, cwd=work), show(theirs, f, cwd=work))
            if fixed != text:
                (work / f).write_text(fixed, encoding="utf-8")
            if both:
                res["files"][f] = "by key"
                res["notes"].append(f"{Path(f).name}: written differently on both sides, upstream's row kept: "
                                    + "; ".join(repr(s) for s in both[:3]) + (f" and {len(both) - 3} more" if len(both) > 3 else ""))
        else:
            drop_exact_duplicate_rows(work / f)
        problems += lint_catalog(work / f, repeated_keys(show(ours, f, cwd=work), show(theirs, f, cwd=work)) if level == "all" else frozenset())
    if level == "all" and PARITY in merged and (work / PARITY).exists():
        problems += check_parity(work / PARITY, show(ours, PARITY, cwd=work), show(theirs, PARITY, cwd=work))
    attribution_hashes(work, True)
    still = attribution_hashes(work, False)
    if still:
        problems.append(f"ATTRIBUTION hashes still wrong: {still}")
    res["timings"]["resolve"] = round(time.time() - t1, 1)
    if problems:
        return abort("; ".join(problems[:4]))
    git("add", "-A", cwd=work)
    what = ", ".join(conflicted) if conflicted else "no conflicts"
    if level == "pins" or not (res["rust"] or PARITY in res["files"] or any(v == "by key" for v in res["files"].values())):
        body = (f"Mechanical merge ({what}): main's copy of the pinned files, hashes recomputed, both sides' catalog rows kept."
                if conflicted else "Merged cleanly, no conflicts.")
    else:
        body = "Resolved by the keeper:\n" + "".join(f"- {f}: {how}\n" for f, how in sorted(res["files"].items()))
        if res["notes"]:
            body += "\n" + "".join(f"- {n}\n" for n in res["notes"])
        body = body.rstrip("\n")
    res["message"] = f"Merge upstream {BASE} {theirs[:8]} into {label}\n\n{body}"
    git("commit", "-q", "-m", res["message"] + TRAILER, cwd=work)
    res["commit"] = git("rev-parse", "HEAD", cwd=work)
    res["needs_cargo"] = bool(res["rust"])
    res.update(status="merged", detail=what)
    return res


# ---------------------------------------------------------------- rerere training
def train_rerere(level: str, work: Path, heads: list) -> int:
    """Record, in rr-cache, how people resolved the code conflicts of earlier merges on these
    branches (git's rerere-train, only for merges not trained before). Returns how many."""
    if level != "all":
        return 0
    rr = common_dir() / "rr-cache"
    rr.mkdir(exist_ok=True)
    done_file = rr / "keeper-trained.txt"
    done = set(done_file.read_text().split()) if done_file.exists() else set()
    base = f"{UPSTREAM_REMOTE}/{BASE}"
    merges = git("rev-list", "--merges", "--parents", *heads, "--not", base).splitlines()
    n = 0
    for line in merges:
        parts = line.split()
        if len(parts) != 3 or parts[0] in done:
            continue
        m, p1, p2 = parts
        names = git("merge-tree", "--write-tree", "--name-only", "--no-messages", *merge_strategy(level), p1, p2, check=False).splitlines()[1:]
        if any(x and not MECHANICAL.match(x) for x in names):
            git("checkout", "-q", "-f", "--detach", p1, cwd=work)
            subprocess.run(["git", *merge_config(level), "merge", "--no-commit", "-q", *merge_strategy(level), p2],
                           cwd=work, capture_output=True)
            if git("diff", "--name-only", "--diff-filter=U", cwd=work):
                git("checkout", "-q", m, "--", ".", cwd=work)
                subprocess.run(["git", "-c", "rerere.enabled=true", "rerere"], cwd=work, capture_output=True)
                n += 1
            git("reset", "-q", "--hard", cwd=work, check=False)        # as git's rerere-train does
        done.add(m)
    done_file.write_text("\n".join(sorted(done)) + "\n")
    return n


# ---------------------------------------------------------------- the cargo checks
def cargo(args: list, cwd: Path, log: Path) -> tuple:
    """Run cargo with its output in a file (a pipe can fill and block); (code, seconds)."""
    t0 = time.time()
    env = dict(os.environ, CARGO_TARGET_DIR=str(TARGET), CARGO_TERM_COLOR="never", CARGO_INCREMENTAL="0")
    with open(log, "w", encoding="utf-8", errors="replace") as f:
        r = subprocess.run(["cargo", *args], cwd=cwd, stdout=f, stderr=subprocess.STDOUT, env=env)
    return r.returncode, round(time.time() - t0, 1)


def tail(log: Path, n: int = 12) -> str:
    lines = [l for l in log.read_text(encoding="utf-8", errors="replace").splitlines() if l.strip()]
    errs = [l for l in lines if l.startswith(("error", "test result", "failures:", "---- ")) or "panicked" in l]
    return " | ".join((errs or lines)[-n:])[:600]


def packages(work: Path) -> list:
    meta = json.loads(run("cargo", "metadata", "--no-deps", "--format-version", "1", cwd=work))
    out = []
    for p in meta["packages"]:
        if p["id"] in meta["workspace_members"]:
            out.append({"name": p["name"], "manifest": p["manifest_path"], "targets": p["targets"],
                        "dir": str(Path(p["manifest_path"]).resolve().parent.relative_to(work.resolve()))})
    return sorted(out, key=lambda p: -len(p["dir"]))


def test_plan(files: list, pkgs: list) -> list:
    """[(package, cargo test arguments)] for the crates the resolved files are in."""
    touched = collections.defaultdict(list)
    for f in files:
        for p in pkgs:
            if p["dir"] in (".", "") or f == p["dir"] or f.startswith(p["dir"] + "/"):
                if p["dir"] in (".", ""):
                    break                              # the root manifest: the workspace check only
                touched[p["name"]].append(f[len(p["dir"]) + 1:])
                break
    plan = []
    for p in pkgs:
        rels = touched.get(p["name"])
        if not rels:
            continue
        kinds = {k for t in p["targets"] for k in t["kind"]}
        tests = {t["name"]: t for t in p["targets"] if "test" in t["kind"]}
        args = ["-p", p["name"]]
        if kinds & {"lib", "rlib", "proc-macro", "cdylib", "staticlib", "dylib"}:
            args.append("--lib")
        elif "bin" in kinds:
            args.append("--bins")
        src_touched = any(not r.startswith("tests/") for r in rels)
        chosen = set()
        for r in rels:
            if r.startswith("tests/"):
                rest = r[len("tests/"):]
                name = rest[:-3] if "/" not in rest and rest.endswith(".rs") else rest.split("/")[0]
                if name in tests:
                    chosen.add(name)
                else:
                    chosen |= set(tests)               # a shared helper or fixture: every program
        if src_touched:
            chosen |= set(tests) if len(tests) <= TEST_TARGET_LIMIT else {n for n in tests if n in GROUPED_TESTS}
        if len(chosen) == len(tests) and tests:
            args.append("--tests")
        else:
            for n in sorted(chosen):
                args += ["--test", n]
        plan.append((p["name"], args))
    return plan


def verify_branch(item: dict, work: Path, logs: Path) -> dict:
    """rustfmt, clippy over the workspace (errors anywhere, warnings in the touched crates), and
    the touched crates' tests, on the merge commit. {ok, detail, timings, checks}"""
    git("checkout", "-q", "-f", "--detach", item["commit"], cwd=work)
    timings, checks = {}, []
    name = item["branch"].replace("/", "-")
    code, s = cargo(["fmt", "--all", "--", "--check"], work, logs / f"{name}-fmt.log")
    timings["fmt"] = s
    if code:
        return {"ok": False, "detail": f"rustfmt: {tail(logs / f'{name}-fmt.log', 4)}", "timings": timings, "checks": checks}
    checks.append("cargo fmt --check")
    pkgs = packages(work)
    plan = test_plan(item["rust"], pkgs)
    touched = {n for n, _ in plan}
    name_of = {str(Path(p["manifest"]).resolve()): p["name"] for p in pkgs}
    log = logs / f"{name}-clippy.log"
    code, s = cargo(["clippy", "--locked", "--workspace", "--all-targets", "--message-format=json"], work, log)
    timings["clippy"] = s
    errors, warnings = [], []
    for line in log.read_text(encoding="utf-8", errors="replace").splitlines():
        if not line.startswith("{"):
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            continue
        if msg.get("reason") != "compiler-message":
            continue
        m = msg.get("message") or {}
        text = (m.get("rendered") or m.get("message") or "").strip().splitlines()
        first = text[0] if text else ""
        if re.match(r"^(warning|error): .*(warnings? emitted|previous errors?|aborting due)", first):
            continue
        pkg = name_of.get(str(Path(msg.get("manifest_path", "")).resolve()), "")
        if m.get("level") == "error":
            errors.append(first)
        elif m.get("level") == "warning" and pkg in touched:
            warnings.append(f"{pkg}: {first}")
    if code and not errors:
        errors.append(tail(log, 3))
    if errors or warnings:
        what = errors[:2] or warnings[:2]
        return {"ok": False, "detail": "clippy: " + " | ".join(what)[:400], "timings": timings, "checks": checks}
    checks.append("cargo clippy --workspace --all-targets (warnings denied in " + (", ".join(sorted(touched)) or "no crate") + ")")
    t0 = time.time()
    for pkg, args in plan:
        log = logs / f"{name}-test-{pkg}.log"
        code, s = cargo(["test", "--locked", *args], work, log)
        timings[f"test {pkg}"] = s
        if code:
            return {"ok": False, "detail": f"cargo test {' '.join(args)}: {tail(log)}", "timings": timings, "checks": checks}
        checks.append("cargo test " + " ".join(args))
    timings["tests"] = round(time.time() - t0, 1)
    return {"ok": True, "detail": "", "timings": timings, "checks": checks}


# ---------------------------------------------------------------- commands
def open_branches(author: str | None) -> list:
    args = ["gh", "pr", "list", "--repo", UPSTREAM_REPO, "--state", "open", "--limit", "500", "--json", "number,headRefName,author"]
    if author:
        args += ["--author", author]
    prs = json.loads(run(*args))
    return sorted((p["number"], p["headRefName"]) for p in prs)


def kinds_of(files: list) -> list:
    out = set()
    for f in files:
        if CATALOG.match(f):
            out.add("catalogs")
        elif f in ("ROADMAP.md", "docs/gaps.md"):
            out.add("notes")
        elif f.startswith("ATTRIBUTION"):
            out.add("attribution")
        elif f == "Cargo.lock":
            out.add("lock")
        elif f == PARITY:
            out.add("parity")
        else:
            out.add("code" if RUST_SIDE.search(f) else "text")
    return sorted(out)


def cmd_classify() -> dict:
    t0 = time.time()
    git("fetch", "-q", UPSTREAM_REMOTE, BASE)
    git("fetch", "-q", FORK_REMOTE)
    base_sha = git("rev-parse", f"{UPSTREAM_REMOTE}/{BASE}")
    items = []
    if REPLAY:
        for sha in REPLAY:
            parents = git("rev-list", "--parents", "-n", "1", sha).split()
            if len(parents) != 3:
                say(f"{sha}: not a merge of two parents; left out")
                continue
            items.append({"number": 0, "branch": f"replay {sha[:8]}", "head": parents[1], "theirs": parents[2], "replay": parents[0]})
    else:
        for number, branch in open_branches(os.environ.get("PR_AUTHOR") or None):
            if ONLY and branch not in ONLY:
                continue
            item = {"number": number, "branch": branch, "theirs": base_sha}
            if branch in SKIP:
                item.update(status="skip", detail="on the skip list")
            elif git("rev-parse", "-q", "--verify", f"{FORK_REMOTE}/{branch}", check=False) == "":
                item.update(status="skip", detail=f"no branch {branch} on {FORK_REMOTE}")
            else:
                item["head"] = git("rev-parse", f"{FORK_REMOTE}/{branch}")
            items.append(item)
    with union_attributes():
        for item in items:
            if item.get("status"):
                continue
            if subprocess.run(["git", "merge-base", "--is-ancestor", item["theirs"], item["head"]]).returncode == 0:
                item.update(status="current", detail="already contains the base branch")
                continue
            names = git("merge-tree", "--write-tree", "--name-only", "--no-messages", *merge_strategy(LEVEL),
                        item["head"], item["theirs"], check=False).splitlines()[1:]
            item["conflicts"] = [n for n in names if n]
            item["kinds"] = kinds_of(item["conflicts"])
    needs_mergiraf = LEVEL == "all" and any(set(i.get("kinds", [])) & {"code", "text"} for i in items)
    lock = hashlib.sha256((show(base_sha, "Cargo.lock") or "").encode()).hexdigest()[:16]
    state = {"level": LEVEL, "base": base_sha, "push": PUSH, "items": items, "lock": lock,
             "timings": {"classify": round(time.time() - t0, 1)}, "needs_mergiraf": needs_mergiraf}
    save_state(state)
    for i in items:
        say(f"#{i['number']} {i['branch']}: {i.get('status') or 'to merge'}"
            + (f" (conflicts: {', '.join(i['conflicts'])})" if i.get("conflicts") else ""))
    output(needs_mergiraf=str(needs_mergiraf).lower(), lock=lock)
    return state


def with_work(fn):
    """Run fn(work) with the scratch worktree (made when missing)."""
    if not (WORK / ".git").exists():
        if WORK.exists():
            shutil.rmtree(WORK)
        git("worktree", "prune")
        git("worktree", "add", "-q", "--detach", str(WORK), "HEAD")
    return fn(WORK)


def cmd_resolve(state: dict) -> dict:
    t0 = time.time()

    def go(work: Path):
        if any(set(i.get("kinds", [])) & {"code", "text"} for i in state["items"]) and LEVEL == "all" and not REPLAY:
            t = time.time()
            heads = [i["head"] for i in state["items"] if i.get("head")]
            n = train_rerere(LEVEL, work, heads)
            state["timings"]["rerere training"] = round(time.time() - t, 1)
            state["rerere_trained"] = n
        for item in state["items"]:
            if item.get("status"):
                continue
            try:
                res = merge_one(item["head"], item["theirs"], item["branch"].removeprefix("replay "), LEVEL, work)
            except RuntimeError as e:
                git("merge", "--abort", cwd=work, check=False)
                res = {"status": "error", "detail": str(e)[:200]}
            item.update(res)
            if item.get("commit") and not item.get("replay"):
                git("update-ref", f"refs/keeper/{item['branch']}", item["commit"])
            say(f"#{item['number']} {item['branch']}: {item['status']} {item['detail']}"
                + (" (cargo checks next)" if item.get("needs_cargo") else ""))
            if item.get("replay"):
                compare_replay(item, work)
    with union_attributes():
        with_work(go)
    state["timings"]["resolve"] = round(time.time() - t0, 1)
    needs_cargo = any(i.get("needs_cargo") for i in state["items"])
    state["needs_cargo"] = needs_cargo
    save_state(state)
    output(needs_cargo=str(needs_cargo).lower())
    return state


def compare_replay(item: dict, work: Path) -> None:
    """For a replayed merge: the files where the keeper's result differs from what was committed."""
    committed = item["replay"]
    if item.get("commit"):
        diff = git("diff", "--name-only", item["commit"], committed, cwd=work).splitlines()
        conflicted = set(item.get("files", {}))
        item["compare"] = {"same": sorted(conflicted - set(diff)), "differs": sorted(conflicted & set(diff)),
                           "other": sorted(set(diff) - conflicted)}
    else:
        item["compare"] = {}
    say(f"   compare with {committed[:8]}: {json.dumps(item['compare'])}")


def cmd_verify(state: dict) -> dict:
    if not state.get("needs_cargo") or not CARGO_CHECKS:
        return state
    logs = _TMP / "keep-prs-logs"
    logs.mkdir(exist_ok=True)
    t0 = time.time()

    def go(work: Path):
        for item in state["items"]:
            if not item.get("needs_cargo") or item.get("status") != "merged":
                continue
            say(f"#{item['number']} {item['branch']}: cargo checks for {', '.join(item['rust'])}")
            v = verify_branch(item, work, logs)
            item["verify"] = v
            item.setdefault("timings", {}).update(v["timings"])
            if v["ok"]:
                item["checks"] = v["checks"]
                say(f"   passed in {sum(x for k, x in v['timings'].items() if k != 'tests'):.0f} s")
            else:
                item.update(status="by hand", detail=f"resolved, but the checks failed: {v['detail']}", commit="")
                git("update-ref", "-d", f"refs/keeper/{item['branch']}", check=False)
                say(f"   failed: {v['detail']}")
    with_work(go)
    state["timings"]["verify"] = round(time.time() - t0, 1)
    save_state(state)
    return state


def cmd_finish(state: dict) -> int:
    rows = []
    for item in state["items"]:
        pushed = ""
        if item.get("status") == "merged" and item.get("commit") and not item.get("replay"):
            if PUSH:
                git("fetch", "-q", FORK_REMOTE, item["branch"], check=False)
                now = git("rev-parse", f"{FORK_REMOTE}/{item['branch']}", check=False)
                if now != item["head"]:
                    item["status"], pushed = "skip", f"the branch moved during the run ({now[:8]}); next run"
                else:
                    git("push", "-q", FORK_REMOTE, f"{item['commit']}:refs/heads/{item['branch']}")
                    pushed = "pushed"
            else:
                pushed = "dry run: not pushed"
        item["pushed"] = pushed
        rows.append(item)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    total = {k: v for k, v in state.get("timings", {}).items()}
    lines = [f"### Keep pull requests current ({'push' if PUSH else 'dry run'}, level {state.get('level')}), "
             f"base {BASE} {state.get('base', '')[:8]}\n",
             "Phases: " + ", ".join(f"{k} {v:.0f} s" for k, v in total.items())
             + (f"; rerere learned from {state['rerere_trained']} earlier merges" if state.get("rerere_trained") is not None else "") + "\n",
             "| PR | branch | result | kinds | files | checks | time | detail |", "|---|---|---|---|---|---|---|---|"]
    for i in rows:
        files = "<br>".join(f"{f}: {h}" for f, h in sorted(i.get("files", {}).items()))
        if i.get("notes"):
            files += "<br>" + "<br>".join(i["notes"])
        t = i.get("timings", {})
        tm = ", ".join(f"{k} {v:.0f}s" for k, v in t.items() if k != "tests")
        comp = ""
        if i.get("replay") and i.get("compare") is not None:
            c = i["compare"]
            comp = f" · vs committed {i['replay'][:8]}: same {len(c.get('same', []))}, differs {c.get('differs', [])}, other {len(c.get('other', []))}"
        lines.append(f"| #{i.get('number')} | {i['branch']} | {i.get('status')} {i.get('pushed', '')} | {', '.join(i.get('kinds', []))} | "
                     f"{files.replace('|', '/')} | {'<br>'.join(i.get('checks', []))} | {tm} | {str(i.get('detail', '')).replace('|', '/')}{comp} |")
    text = "\n".join(lines) + "\n"
    for i in rows:
        say(f"#{i.get('number')} {i['branch']}: {i.get('status')} {i.get('detail', '')} {i.get('pushed', '')}".rstrip())
    say("\n" + text)
    if summary:
        with open(summary, "a", encoding="utf-8") as f:
            f.write(text)
    save_state(state)
    if (WORK / ".git").exists() and not os.environ.get("KEEPER_KEEP_WORK"):
        git("worktree", "remove", "--force", str(WORK), check=False)
    return 1 if any(i.get("status") == "error" for i in rows) else 0


def main(argv: list) -> int:
    cmd = argv[1] if len(argv) > 1 else "run"
    if cmd == "replay":
        global REPLAY
        REPLAY = argv[2:] or REPLAY
        cmd = "run"
    if cmd == "classify":
        cmd_classify()
        return 0
    if cmd == "resolve":
        cmd_resolve(load_state())
        return 0
    if cmd == "verify":
        cmd_verify(load_state())
        return 0
    if cmd == "finish":
        return cmd_finish(load_state())
    if cmd != "run":
        sys.exit(f"unknown command {cmd}")
    state = cmd_classify()
    state = cmd_resolve(state)
    state = cmd_verify(state)
    return cmd_finish(state)


if __name__ == "__main__":
    import signal
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))   # so the finally blocks still run
    sys.exit(main(sys.argv))
