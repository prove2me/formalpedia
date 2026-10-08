-- Prove2me | Theorems.Thm_AvramDividend_Classical_neg_jump_exp_over_theta_bound
-- name    : AvramDividend.Classical.neg_jump_exp_over_theta_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:54:20.27368+00:00
-- url     : https://prove2.me/theorems/7730d72a-dd13-4950-9ba0-58dc042feaac
-- title:
--   Normalized exponential decay is dominated by absolute negative jump size
-- statement:
--   For theta positive and y nonpositive, the normalized negative exponential deficit (1-exp(theta*y))/theta lies between zero and -y. This supplies the uniform integrable majorant used in the dominated-convergence proof of the bounded-variation Lévy exponent asymptotic.
-- source:
--   Monotonicity and tangent inequality of the real exponential in pinned Mathlib. Only elementary scalar assumptions, with process integrability handled separately.

import Mathlib

namespace AvramDividend.Classical
theorem neg_jump_exp_over_theta_bound
    (θ y : ℝ) (hθ : 0 < θ) (hy : y ≤ 0) :
    0 ≤ (1 - Real.exp (θ * y)) / θ ∧
      (1 - Real.exp (θ * y)) / θ ≤ -y := by
  sorry
end AvramDividend.Classical
