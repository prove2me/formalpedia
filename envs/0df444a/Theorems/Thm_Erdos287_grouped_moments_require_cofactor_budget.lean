-- Prove2me | Theorems.Thm_Erdos287_grouped_moments_require_cofactor_budget
-- name    : Erdos287.grouped_moments_require_cofactor_budget
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:33:58.813862+00:00
-- url     : https://prove2.me/theorems/d7ec830b-c415-5911-b08b-b34159142250
-- title:
--   Cofactor budget required by the grouped first and second moment test
-- statement:
--   Let $N\ge11$, $0\le T\le2BN$, $0\le\sigma\le1/4$, and $18/5\le A<r\le93/25$. If the normalized mean per group $\mu$ satisfies $N\mu\le2\sigma\log(1+T)$ and $1-A\sigma<\mu(r-A)$, then $\log(1+22B)>55/3$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.grouped_moments_require_cofactor_budget (N B T σ r A μ : ℝ)
    (hN : 11 ≤ N) (hB : 0 ≤ B) (hT : 0 ≤ T ∧ T ≤ 2 * B * N)
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hA : 18 / 5 ≤ A) (hAr : A < r)
    (hr : r ≤ 93 / 25) (hmean : N * μ ≤ 2 * σ * Real.log (1 + T))
    (hsieve : 1 - A * σ < μ * (r - A)) :
    (55 / 3 : ℝ) < Real.log (1 + 22 * B) := by sorry
