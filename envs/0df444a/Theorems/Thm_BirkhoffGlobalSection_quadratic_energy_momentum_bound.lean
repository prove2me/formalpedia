-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_quadratic_energy_momentum_bound
-- name    : BirkhoffGlobalSection.quadratic_energy_momentum_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:32:51.752352+00:00
-- url     : https://prove2.me/theorems/e21a3fe2-16ad-47a3-a4f5-800b40287ef9
-- statement:
--   Let $K\geq0$, and suppose the coefficients $A,B$ satisfy $|A|,|B|\leq K$ while the constant term satisfies $C\geq-K$. If $$\frac{p^2+q^2}{2}+Ap+Bq+C\leq0,$$ then $|p|,|q|\leq4(K+1)$. This coercivity bound applies to regularized Hamiltonians after their position-dependent coefficients have been bounded.
-- source:
--   Elementary quadratic coercivity estimate used with Joung–van Koert, Equation (2.2), https://arxiv.org/abs/2407.19159v3.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace BirkhoffGlobalSection
theorem quadratic_energy_momentum_bound (K A B C p q : ℝ)
    (hK : 0 ≤ K) (hA : |A| ≤ K) (hB : |B| ≤ K) (hC : -K ≤ C)
    (henergy : (p ^ 2 + q ^ 2) / 2 + A * p + B * q + C ≤ 0) :
    |p| ≤ 4 * (K + 1) ∧ |q| ≤ 4 * (K + 1) := by sorry
end BirkhoffGlobalSection
