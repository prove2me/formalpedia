-- Prove2me | Theorems.Thm_Erdos624_linear_ingredient_iff
-- name    : Erdos624.linear_ingredient_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:29:17.013525+00:00
-- url     : https://prove2.me/theorems/3ff1ce22-6d7a-4b4b-b77d-602232a71f5a
-- title:
--   Invertible $T$ on $\mathbb F_2^d$ with $I+T$ invertible exists iff $d\ne1$ (Erdős 624 cross-review)
-- statement:
--   For a natural number $d$ there is a linear map $T:\mathbb F_2^d\to\mathbb F_2^d$ such that both $T$ and $I+T$ are bijective **if and only if** $d\neq1$. (For $d=0$ the space is trivial; for $d=1$ the only invertible map is $T=I$, and then $I+T=0$.)
--
--   This is the linear ingredient of the cross-review's local counterexample (blocks $E^1=\{p,q\}\cup\mathrm{supp}(z)$, $E^2=\{q,r\}\cup\mathrm{supp}(Tz)$, $E^3=\{p,r\}\cup\mathrm{supp}((I+T)z)$), used there with $d=k-6\ge58$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem linear_ingredient_iff (d : ℕ) :
    (∃ T : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2),
      Function.Bijective T ∧ Function.Bijective (fun v => v + T v)) ↔ d ≠ 1 := by sorry

end Erdos624
