-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_deriv_eq_continuous_product_Ioi
-- name    : AvramDividend.Classical.contDiffOn_one_of_deriv_eq_continuous_product_Ioi
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T13:40:39.299595+00:00
-- url     : https://prove2.me/theorems/5350cb84-ba0a-4175-9251-da98c2bf41df
-- title:
--   A continuous logarithmic derivative coefficient gives C1 regularity on the positive half-line
-- statement:
--   If W is differentiable at every positive point with derivative W'(x)=g(x)W(x), and g is continuous on (0,∞), then W is continuously differentiable there. Differentiability gives continuity of W; hence gW is continuous, so the derivative is continuous. This is the deterministic calculus bridge for the excursion-height representation W'(x)=n(height≥x)W(x).
-- source:
--   Pinned Mathlib contDiffOn_one_iff_derivWithin, uniqueDiffOn_Ioi, derivWithin_of_isOpen and ContinuousOn.congr.

import Mathlib
open Set

theorem AvramDividend.Classical.contDiffOn_one_of_deriv_eq_continuous_product_Ioi
    (W g : ℝ → ℝ)
    (hg : ContinuousOn g (Ioi 0))
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt W (g x * W x) x) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
