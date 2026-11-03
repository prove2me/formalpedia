-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_past_rectangle_of_measurable_extractor
-- name    : AvramDividend.Classical.avram_wave7_01_bv_negative_mark_past_rectangle_of_measurable_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:06:24.178083+00:00
-- url     : https://prove2.me/theorems/b40844ea-f6e0-4409-b3aa-9caf2f7aaeb4
-- title:
--   Original BV finite-activity negative-mark predictable rectangle has exact positive rate once the same-path extractor is measurable
-- statement:
--   For the literal original SpectrallyNegativeLevy P 𝓕, under BV and the additional finite negative-jump rate hypothesis X.ν(Iio 0)<∞, any strictly-positive-start source jump count with all strictly negative marks has exact predictable rectangle expectation P(A)(t-s)ν(Iio 0) against every A in the original filtration 𝓕_s, provided its same-path future extractor F has been shown measurable and equal to the intrinsic count. This imports a genuinely proved original expected negative count theorem and the separate future/past factorisation helper. It does not assert the still-open arbitrary Borel mark result and explicitly records the extractor measurability premise.
-- source:
--   Proved source negative-mark exact gap-rate c7a926f3-2b09-4614-ae82-f607fc1a0058 and Wave7-01 original source conditional factorisation helper ad24b83b-aa01-4fe1-a792-380fdb3e7329. The latter was Open with remote proof verification in flight on 2 November 2026; a reduction depending on it is not a Proved theorem until it closes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_negative_mark_past_rectangle_of_measurable_extractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hExtract : ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) =
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
    P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
