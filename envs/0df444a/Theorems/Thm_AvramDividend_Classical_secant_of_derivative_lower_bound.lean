-- Prove2me | Theorems.Thm_AvramDividend_Classical_secant_of_derivative_lower_bound
-- name    : AvramDividend.Classical.secant_of_derivative_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:53:23.63099+00:00
-- url     : https://prove2.me/theorems/5459ff1b-7801-4c7d-95b1-dcec91dcb241
-- title:
--   A derivative lower bound gives all secant inequalities on a nonnegative interval
-- statement:
--   Suppose W is continuous on [0,c] and differentiable on (0,c), with its derivative everywhere at least the real constant d on (0,c). Then for any 0≤b≤x≤c, W(x)-W(b)≥(x-b)d. The endpoints, including b=0 and x=c, are handled using continuity. This isolates the calculus needed to compare the canonical barrier with smaller rival dividend barriers in Avram Proposition 3(i).
-- source:
--   Ordinary mean value inequality; Mathlib convex_Icc.mul_sub_le_image_sub_of_le_deriv. The source-reviewed code for this lemma is in artifacts/m2m4/milestone_campaign_20261004/m3/conditional_barrier_comparison.lean, and the inequality is needed for cstar_scale_derivative_shape.

import Mathlib
open Set

theorem AvramDividend.Classical.secant_of_derivative_lower_bound
    (W : ℝ → ℝ) (c d : ℝ)
    (hcont : ContinuousOn W (Set.Icc 0 c))
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 c))
    (hderiv : ∀ t ∈ Set.Ioo 0 c, d ≤ deriv W t) :
    ∀ b x : ℝ, 0 ≤ b → b ≤ x → x ≤ c →
      (x - b) * d ≤ W x - W b := by sorry
