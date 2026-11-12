-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite74_cap_gap_of_grad
-- name    : AvramDividend.Classical.avram_gfinite74_cap_gap_of_grad
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:46:13.983411+00:00
-- url     : https://prove2.me/theorems/35870c77-591f-4df6-8522-7b3c1de9450d
-- title:
--   Nonnegative finite-cap cash defect from marginal value at least one
-- statement:
--   If w is continuous on the closed interval [a,b], differentiable in its interior and its derivative is everywhere at least one in the interior, the upper-cap secant defect (w(b)-w(a))-(b-a) is nonnegative. Reduces to cap excess monotonicity and its algebraic endpoint inequality.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_gfinite74_cap_gap_of_grad
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : ∀ z ∈ Ioo a b, DifferentiableAt ℝ w z)
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    0 ≤ (w b - w a) - (b - a) := by
  sorry
