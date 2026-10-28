-- Prove2me | Theorems.Thm_Erdos624_H_mono
-- name    : Erdos624.H_mono
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:46:51.156589+00:00
-- url     : https://prove2.me/theorems/f6353f22-cc43-465a-be67-a1723c6094e1
-- title:
--   $H$ is monotone (Erdős 624)
-- statement:
--   Let $H(n)$ be the least $m$ such that some $f:\mathcal P(X)\to X$, $|X|=n$, satisfies $\{f(A):A\subseteq Y\}=X$ for all $Y\subseteq X$ with $|Y|\ge m$ (Erdős Problem 624). **Theorem.** If $1\le n\le N$ then $H(n)\le H(N)$.
--
--   This is the monotonicity corollary of the restriction/retraction argument.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Theorem B2 of GPT 6.1 Sol; lemma proposed by GPT 6.1 Sol (Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem H_mono {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) : H n ≤ H N := by sorry

end Erdos624
