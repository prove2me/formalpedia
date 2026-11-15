-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a251_positive_interval_lower_derivative_bounds_value_above_near_origin
-- name    : AvramDividend.Classical.avram_ga_a251_positive_interval_lower_derivative_bounds_value_above_near_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:43:24.517192+00:00
-- url     : https://prove2.me/theorems/861ed050-19a3-4f05-9dbd-3d48fcf1290c
-- title:
--   Gaussian near-origin compact interval derivative lower bound controls scalar value from above
-- statement:
--   On any strictly positive reserve compact interval from y to a, if the scalar transformed Gaussian HJB candidate is continuous, differentiable in the interior and has first derivative bounded below by -M, then its value at y is bounded above by its value at a plus M(a-y). This is the mean-value step needed to turn the antitone HJB exponential first-order factor a250 into a uniform one-sided positive-reserve upper envelope near ruin zero in a216, without invoking the undefined value w(0).
-- source:
--   Mathlib Convex.mul_sub_le_image_sub_of_le_deriv and original Gaussian HJB near-origin upper-barrier argument

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a251_positive_interval_lower_derivative_bounds_value_above_near_origin
    (h : ℝ → ℝ) (a y M : ℝ)
    (hya : y ≤ a)
    (hCont : ContinuousOn h (Set.Icc y a))
    (hDiff : DifferentiableOn ℝ h (interior (Set.Icc y a)))
    (hLower : ∀ t ∈ interior (Set.Icc y a),
      -M ≤ deriv h t) :
    h y ≤ h a + M*(a-y) := by sorry
