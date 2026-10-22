#!/usr/bin/env python3
"""Keep a contributor's open pull requests mergeable while the base branch moves.

Every upstream change to a translation catalog changes the SHA-256 pinned for it in
ATTRIBUTION.toml, so each open pull request that also edits that file (or holds an older copy)
shows a conflict after almost every upstream commit. The conflict is mechanical, and this script
resolves exactly that kind and nothing else:

  * translation catalogs (crates/ui-egui/src/i18n/*.tsv), ROADMAP.md and docs/gaps.md: both
    sides' lines are kept (git's union merge); the catalogs are then checked for rows with the
    wrong number of columns and for the same key translated twice;
  * ATTRIBUTION.toml: the base branch's copy, with every [[asset]] sha256 recomputed from the
    file it names;
  * Cargo.lock: the base branch's copy, re-resolved for the workspace only;
  * anything else that conflicts: the merge is abandoned and the branch is listed for a person.

It only ever adds a merge commit on top of the branch (no rebase, no force push), and it leaves
a branch alone when it already contains the base branch. Dry run by default: it merges in a
scratch worktree, reports what it would push, and pushes nothing unless PUSH=1.

Environment:
  UPSTREAM_REPO     owner/name of the repository the pull requests are open on (storytold/pdfcraft)
  PR_AUTHOR         only pull requests by this login (default: the repository owner of FORK_REMOTE)
  UPSTREAM_REMOTE   git remote of the base repository (default: upstream)
  FORK_REMOTE       git remote holding the pull request branches (default: origin)
  BASE              base branch (default: main)
  ONLY              comma-separated branch names to handle (default: all open pull requests)
  PUSH              1 to push the merge commits (default: dry run)
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

UPSTREAM_REPO = os.environ.get("UPSTREAM_REPO", "storytold/pdfcraft")
UPSTREAM_REMOTE = os.environ.get("UPSTREAM_REMOTE", "upstream")
FORK_REMOTE = os.environ.get("FORK_REMOTE", "origin")
BASE = os.environ.get("BASE", "main")
PUSH = os.environ.get("PUSH", "") == "1"
ONLY = {b.strip() for b in os.environ.get("ONLY", "").split(",") if b.strip()}
CATALOGS = "crates/ui-egui/src/i18n/"
UNION_PATHS = (CATALOGS + "*.tsv", "ROADMAP.md", "docs/gaps.md")
MECHANICAL = re.compile(r"^(crates/ui-egui/src/i18n/[^/]+\.tsv|ATTRIBUTION\.toml|ATTRIBUTION\.md|ROADMAP\.md|docs/gaps\.md|Cargo\.lock)$")
TRAILER = "\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"


def run(*args: str, cwd: Path | None = None, check: bool = True, inp: str | None = None) -> str:
    r = subprocess.run(args, cwd=cwd, capture_output=True, text=True, input=inp)
    if check and r.returncode:
        raise RuntimeError(f"{' '.join(args)}: {r.stderr.strip() or r.stdout.strip()}")
    return r.stdout.strip()


def git(*args: str, cwd: Path | None = None, check: bool = True) -> str:
    return run("git", *args, cwd=cwd, check=check)


def lint_catalog(path: Path) -> list:
    """Problems in one catalog: rows without 3 columns, and a key translated twice."""
    problems, seen = [], {}
    for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        cols = line.split("\t")
        if len(cols) != 3:
            problems.append(f"{path.name}:{n}: {len(cols)} columns, not 3")
            continue
        key = (cols[0], cols[1])
        if key in seen and seen[key] != line:
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


def open_branches(author: str | None) -> list:
    args = ["gh", "pr", "list", "--repo", UPSTREAM_REPO, "--state", "open", "--limit", "500", "--json", "number,headRefName,author"]
    if author:
        args += ["--author", author]
    prs = json.loads(run(*args))
    return sorted((p["number"], p["headRefName"]) for p in prs)


def handle(number: int, branch: str, base_sha: str, work: Path) -> tuple:
    """(status, detail). Leaves the merge commit in `work` (detached) when it made one."""
    ref = f"{FORK_REMOTE}/{branch}"
    if git("rev-parse", "-q", "--verify", ref, cwd=work, check=False) == "":
        return "skip", f"no branch {branch} on {FORK_REMOTE}"
    head = git("rev-parse", ref, cwd=work)
    if subprocess.run(["git", "merge-base", "--is-ancestor", base_sha, head], cwd=work).returncode == 0:
        return "current", "already contains the base branch"
    git("checkout", "-q", "--detach", head, cwd=work)
    r = subprocess.run(["git", "-c", "rerere.enabled=false", "merge", "--no-ff", "--no-commit", "-q", base_sha], cwd=work, capture_output=True, text=True)
    conflicted = git("diff", "--name-only", "--diff-filter=U", cwd=work).split()
    by_hand = [f for f in conflicted if not MECHANICAL.match(f)]
    if by_hand:
        git("merge", "--abort", cwd=work, check=False)
        return "by hand", ", ".join(by_hand)
    if r.returncode and not conflicted:
        git("merge", "--abort", cwd=work, check=False)
        return "by hand", (r.stderr or r.stdout).strip()[:200]
    for f in conflicted:
        if f in ("ATTRIBUTION.toml", "ATTRIBUTION.md", "Cargo.lock"):
            git("checkout", "--theirs", f, cwd=work)
    if "Cargo.lock" in conflicted:
        subprocess.run(["cargo", "update", "-w", "-q"], cwd=work, capture_output=True)
    problems = []
    merged = git("diff", "--name-only", "--cached", cwd=work).split() + conflicted
    for f in sorted(set(merged)):
        if f.startswith(CATALOGS) and f.endswith(".tsv") and (work / f).exists():
            drop_exact_duplicate_rows(work / f)
            problems += lint_catalog(work / f)
    attribution_hashes(work, True)
    left = attribution_hashes(work, False)
    if left:
        problems.append(f"ATTRIBUTION hashes still wrong: {left}")
    if problems:
        git("merge", "--abort", cwd=work, check=False)
        return "by hand", "; ".join(problems[:4])
    git("add", "-A", cwd=work)
    what = ", ".join(conflicted) if conflicted else "no conflicts"
    git("-c", "user.name=pr-keeper", "-c", "user.email=pr-keeper@users.noreply.github.com", "commit", "-q", "-m",
        f"Merge upstream {BASE} {base_sha[:8]} into {branch}\n\nMechanical merge ({what}): main's ATTRIBUTION.toml with its hashes recomputed, "
        f"both sides' catalog rows kept.{TRAILER}", cwd=work)
    return "merged", f"{git('rev-parse', '--short', 'HEAD', cwd=work)} ({what})"


def main() -> int:
    git("fetch", "-q", UPSTREAM_REMOTE, BASE)
    git("fetch", "-q", FORK_REMOTE)
    base_sha = git("rev-parse", f"{UPSTREAM_REMOTE}/{BASE}")
    author = os.environ.get("PR_AUTHOR") or None
    rows = []
    with tempfile.TemporaryDirectory(prefix="keep-prs-") as d:
        work = Path(d) / "wt"
        git("worktree", "add", "-q", "--detach", str(work), base_sha)
        attrs = Path(git("rev-parse", "--git-common-dir")) / "info" / "attributes"
        attrs = attrs if attrs.is_absolute() else Path.cwd() / attrs
        attrs.parent.mkdir(parents=True, exist_ok=True)
        old_attrs = attrs.read_text(encoding="utf-8") if attrs.exists() else None
        attrs.write_text((old_attrs or "") + "".join(f"{p} merge=union\n" for p in UNION_PATHS), encoding="utf-8")
        try:
            for number, branch in open_branches(author):
                if ONLY and branch not in ONLY:
                    continue
                try:
                    status, detail = handle(number, branch, base_sha, work)
                except RuntimeError as e:
                    status, detail = "error", str(e)[:200]
                pushed = ""
                if status == "merged":
                    head = git("rev-parse", "HEAD", cwd=work)
                    if PUSH:
                        git("push", "-q", FORK_REMOTE, f"{head}:refs/heads/{branch}", cwd=work)
                        pushed = "pushed"
                    else:
                        pushed = "dry run: not pushed"
                rows.append((number, branch, status, detail, pushed))
                print(f"#{number} {branch}: {status} {detail} {pushed}".rstrip(), flush=True)
        finally:
            if old_attrs is None:
                attrs.unlink(missing_ok=True)
            else:
                attrs.write_text(old_attrs, encoding="utf-8")
            git("worktree", "remove", "--force", str(work), check=False)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as f:
            f.write(f"### Keep pull requests current ({'push' if PUSH else 'dry run'}), base {BASE} {base_sha[:8]}\n\n| PR | branch | result | detail |\n|---|---|---|---|\n")
            for n, b, s, dtl, p in rows:
                f.write(f"| #{n} | {b} | {s} {p} | {dtl} |\n")
    return 1 if any(s == "error" for _, _, s, _, _ in rows) else 0


if __name__ == "__main__":
    sys.exit(main())
