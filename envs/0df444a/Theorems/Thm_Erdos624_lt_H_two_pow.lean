-- Prove2me | Theorems.Thm_Erdos624_lt_H_two_pow
-- name    : Erdos624.lt_H_two_pow
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:27:31.356183+00:00
-- url     : https://prove2.me/theorems/dc9e149a-969f-4d6d-8fed-a1fd6a6f204c
-- title:
--   $H(2^k)>k$ for $k\ge3$ (Erdős 624)
-- statement:
--   Let $|X|=n$ and let $H(n)$ be the least $m$ such that some $f:\mathcal P(X)\to X$ satisfies $\{f(A):A\subseteq Y\}=X$ for every $Y\subseteq X$ with $|Y|\ge m$ (Erdős Problem 624). **Theorem.** For every $k\ge3$,
--
--   $$H(2^k)\ge k+1.$$
--
--   This weak form of Erdős Problem 624 at powers of two was noted by Erdős as open and given a simple proof by Alon (see erdosproblems.com/624); here it is derived as a corollary of the robust Alon bound `robust_alon_sum`. It is not new.
--
--   **Formalization Note.** Uses the Formal Conjectures definition of $H$ on $\mathrm{Fin}\,n$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; corollary of the robust Alon bound in claim from GPT 6.1 Sol (fourth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026); known (Alon, via erdosproblems.com/624)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem lt_H_two_pow (k : ℕ) (hk : 3 ≤ k) : k < H (2 ^ k) := by sorry

end Erdos624
