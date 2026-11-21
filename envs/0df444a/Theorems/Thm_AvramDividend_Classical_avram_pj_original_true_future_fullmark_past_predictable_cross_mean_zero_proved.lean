-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_true_future_fullmark_past_predictable_cross_mean_zero_proved
-- name    : AvramDividend.Classical.avram_pj_original_true_future_fullmark_past_predictable_cross_mean_zero_proved
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:06:55.943494+00:00
-- url     : https://prove2.me/theorems/cb18ab54-680a-4832-836c-37264607020e
-- title:
--   Original full negative Lévy cutoff future physical marked cell has zero cross expectation against past predictable weight
-- statement:
--   For original spectrally negative Lévy X under its true right-continuous filtration, the actual complete negative mark count on a deterministic future physical interval and its exact finite Lévy rate are centred conditional on the past. Any past strongly measurable coefficient with integrable weighted product and integrable compensated future count has zero ordinary cross expectation. The conclusion is a concrete original-space full-negative mark cross-cell isometry component.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_true_future_fullmark_past_predictable_cross_mean_zero_proved
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    ∀ (U : Ω → ℝ),
      StronglyMeasurable[𝓕.rightCont s] U →
      Integrable (fun ω => U ω * ((N ω).toReal - r)) P →
      Integrable (fun ω => (N ω).toReal - r) P →
      (∫ ω, U ω * ((N ω).toReal - r) ∂P) = 0 := by sorry
