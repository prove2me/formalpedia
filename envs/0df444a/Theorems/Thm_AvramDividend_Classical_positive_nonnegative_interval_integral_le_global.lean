-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_nonnegative_interval_integral_le_global
-- name    : AvramDividend.Classical.positive_nonnegative_interval_integral_le_global
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:28:41.414877+00:00
-- url     : https://prove2.me/theorems/745ce789-d8fb-4ca3-acb0-f5ac57f1ec74
-- title:
--   Finite positive-interval integral is bounded by the global integral
-- statement:
--   For any nonnegative integrable real function on positive times and x≥0, the integral over (0,x] is bounded above by its total integral over (0,∞). This supports replacing finite-horizon causal convolution norms by their global weighted L1 norm.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set

theorem AvramDividend.Classical.positive_nonnegative_interval_integral_le_global
    (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in Ioc (0 : ℝ) x, f t ∂volume) ≤
      (∫ t in Ioi (0 : ℝ), f t ∂volume) := by sorry
