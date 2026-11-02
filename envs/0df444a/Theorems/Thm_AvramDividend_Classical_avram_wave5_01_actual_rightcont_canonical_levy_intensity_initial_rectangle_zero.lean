-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_canonical_levy_intensity_initial_rectangle_zero
-- name    : AvramDividend.Classical.avram_wave5_01_actual_rightcont_canonical_levy_intensity_initial_rectangle_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:39:54.03474+00:00
-- url     : https://prove2.me/theorems/62ae8958-8aea-492f-807a-f4139218d87d
-- title:
--   Actual right-continuous source finite-horizon Lévy intensity has zero initial-time predictable rectangles
-- statement:
--   For the genuine original SpectrallyNegativeLevy P 𝓕 and any finite horizon T, construct the canonical finite measure μ on 𝓕.rightCont.predictable that agrees with the horizon-restricted real Lebesgue time mapped to NNReal multiplied by the same P. Then for each actual original right-continuous time-zero event A and Borel mark B, its product with the given X.ν negative-mark restriction charges no initial-time rectangle. This discharges the N-side hBot in source controlled-compensation interfaces without assuming future-rectangle intensity or using a detached process.
-- source:
--   Uses Proved source finite-horizon predictable time-probability measure 16857b34. The time marginal is atomless at zero after restriction to [0,T]; canonical product with X.ν preserves zero, even for infinite Lévy mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_rightcont_canonical_levy_intensity_initial_rectangle_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
        ∀ (B : Set ℝ), MeasurableSet B →
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         μ.prod (X.ν.restrict (Iio (0 : ℝ))))
          (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) = 0) := by sorry
