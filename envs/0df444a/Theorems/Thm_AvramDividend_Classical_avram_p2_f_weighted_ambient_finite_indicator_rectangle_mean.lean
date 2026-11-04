-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ambient_finite_indicator_rectangle_mean
-- name    : AvramDividend.Classical.avram_p2_f_weighted_ambient_finite_indicator_rectangle_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:01.026196+00:00
-- url     : https://prove2.me/theorems/4c99e5f4-2273-4910-bc81-ab27e250ccdf
-- title:
--   Ambient finite simple indicator sums preserve genuine past rectangle means exactly
-- statement:
--   Assume an explicit actual-event first moment for a nonnegative original random count against every event in a past sigma algebra. Then any finite nonnegative combination of past-event indicators applied to that count has an exact ENNReal integral equal to the corresponding weighted sum of event measures times the supplied rate. This proves the finite-simple stage independently of an open Levy intensity theorem, and preserves all 0*infinity cases.
-- source:
--   Mathlib Measurable.indicator, lintegral_finset_sum, lintegral_const_mul, lintegral_indicator and Finset.sum_congr.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_ambient_finite_indicator_rectangle_mean
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℝ≥0∞) (hN : Measurable N)
    (mPast : MeasurableSpace Ω) (hm : mPast ≤ mΩ)
    (r : ℝ≥0∞) (S : Finset ι)
    (A : ι → Set Ω) (c : ι → ℝ≥0∞)
    (hA : ∀ i ∈ S, MeasurableSet[mPast] (A i))
    (hEvent : ∀ E : Set Ω, MeasurableSet[mPast] E →
      (∫⁻ ω in E, N ω ∂μ) = μ E * r) :
    (∫⁻ ω, S.sum (fun i => c i * (A i).indicator N ω) ∂μ) =
    S.sum (fun i => c i * (μ (A i) * r)) := by sorry
