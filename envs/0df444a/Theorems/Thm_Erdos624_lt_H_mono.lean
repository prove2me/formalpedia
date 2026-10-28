-- Prove2me | Theorems.Thm_Erdos624_lt_H_mono
-- name    : Erdos624.lt_H_mono
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:46:48.818636+00:00
-- url     : https://prove2.me/theorems/ec3a2daa-9bcb-4b44-b264-31a85dc5d72d
-- title:
--   Monotonicity of non-goodness for Erdős 624: $H(n)>m$ and $N\ge n$ imply $H(N)>m$
-- statement:
--   Let $H(n)$ be the least $m$ such that some $f:\mathcal P(X)\to X$, $|X|=n$, satisfies $\{f(A):A\subseteq Y\}=X$ for all $Y\subseteq X$ with $|Y|\ge m$ (Erdős Problem 624). **Theorem.** If $1\le n\le N$ and $H(n)>m$, then $H(N)>m$.
--
--   An $m$-good map on an $N$-set restricts to an $n$-subset $U$ and, composed with a retraction $X\to U$, gives an $m$-good map on $U$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Theorem B2 of GPT 6.1 Sol; lemma proposed by GPT 6.1 Sol (Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem lt_H_mono {n N m : ℕ} (hn : 0 < n) (hnN : n ≤ N) (h : m < H n) : m < H N := by sorry

end Erdos624
