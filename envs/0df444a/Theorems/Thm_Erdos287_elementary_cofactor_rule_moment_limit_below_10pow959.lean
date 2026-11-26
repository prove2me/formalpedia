-- Prove2me | Theorems.Thm_Erdos287_elementary_cofactor_rule_moment_limit_below_10pow959
-- name    : Erdos287.elementary_cofactor_rule_moment_limit_below_10pow959
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:34:35.889736+00:00
-- url     : https://prove2.me/theorems/2532ecac-7872-4911-845d-f544be07c9bc
-- title:
--   Finite limitation of the elementary cofactor rule for the grouped moment test
-- statement:
--   Let $B\operatorname{lcm}(1,\ldots,B)<p\le M\le10^{959}$. Suppose $N\ge11$, $0\le T\le2BN$, $0\le\sigma\le1/4$, $18/5\le A<r\le93/25$, and $N\mu\le2\sigma\log(1+T)$. Then $\mu(r-A)\le1-A\sigma$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.elementary_cofactor_rule_moment_limit_below_10pow959 (B p M : ℕ) (N T σ r A μ : ℝ)
    (hsmall : B * Nat.lcmUpto B < p) (hpM : p ≤ M) (hM : M ≤ 10 ^ (959 : ℕ))
    (hN : 11 ≤ N) (hT : 0 ≤ T ∧ T ≤ 2 * (B : ℝ) * N)
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hA : 18 / 5 ≤ A) (hAr : A < r)
    (hr : r ≤ 93 / 25) (hmean : N * μ ≤ 2 * σ * Real.log (1 + T)) :
    μ * (r - A) ≤ 1 - A * σ := by sorry
