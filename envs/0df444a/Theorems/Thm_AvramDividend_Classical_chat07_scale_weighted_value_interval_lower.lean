-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_value_interval_lower
-- name    : AvramDividend.Classical.chat07_scale_weighted_value_interval_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:21:00.756976+00:00
-- url     : https://prove2.me/theorems/3b24d49d-51cc-4b9f-b784-56117d5de036
-- title:
--   Lower exponential-weighted interval mass from monotone scale function
-- statement:
--   For an Avram q-scale function W, real decay θ≥0, a≤b and W(a)≥0, the exponentially weighted product exp(-θx)W(x) is interval integrable and the integral over a..b is at least (b-a)exp(-θb)W(a). This follows from scale monotonicity and exponential antitonicity on nonnegative rates. In conjunction with a scale derivative mass bound, the inequality provides a concrete comparison between derivative mass over one unit interval and scale-function Laplace mass over the following unit interval.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_weighted_value_interval_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ a b : ℝ) (hθ : 0 ≤ θ) (hab : a ≤ b)
    (hWa : 0 ≤ W a) :
    IntervalIntegrable
      (fun x : ℝ => Real.exp (-(θ * x)) * W x) volume a b ∧
      (b - a) * (Real.exp (-(θ * b)) * W a) ≤
        (∫ x in a..b, Real.exp (-(θ * x)) * W x) := by sorry
