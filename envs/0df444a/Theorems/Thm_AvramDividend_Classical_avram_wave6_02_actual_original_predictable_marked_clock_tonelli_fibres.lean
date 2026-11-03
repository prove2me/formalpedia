-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_original_predictable_marked_clock_tonelli_fibres
-- name    : AvramDividend.Classical.avram_wave6_02_actual_original_predictable_marked_clock_tonelli_fibres
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:07:47.656203+00:00
-- url     : https://prove2.me/theorems/f9eebd47-0591-484f-8f72-1bbb5b9494df
-- title:
--   Original right-continuous predictable physical marked clock equals actual nonnegative sample-fibre time-probability Tonelli integral
-- statement:
--   Construct on the original spectrally negative Lévy probability space and rightCont predictable filtration the actual finite horizon physical clock μ, and establish for every predictably measurable nonnegative marked kernel G (also jointly Borel measurable on full time×Ω×marks) the exact identity between its μ×X.ν negative-mark ℓintegral and the iterated original P-sample, actual horizon time and genuine X.ν negative-mark ℓintegral. This is a source-exact Tonelli bridge needed for the pathwise predictable compensator of the stopped C² Taylor jump martingale, independent of the still Open original source rectangle law and without any small-jump first moment.
-- source:
--   Canonical Proved original physical predictable trim clock 16857b34; genuine Lévy negative SFinite from X; pinned lintegral_prod, lintegral_prod_symm, Measurable.lintegral_prod_right, and predicted integral equality hlintegral. This identifies original P-fibres, not a surrogate product probability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_original_predictable_marked_clock_tonelli_fibres
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ G : ((ℝ≥0 × Ω) × ℝ) → ℝ≥0∞,
        Measurable[(@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))] G →
        Measurable G →
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          ∫⁻ p, G p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
        ∫⁻ ω, ∫⁻ t, ∫⁻ z, G ((t, ω), z)
          ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal) ∂P) := by sorry
