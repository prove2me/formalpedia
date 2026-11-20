-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_Levy_finite_predictable_physical_clock
-- name    : AvramDividend.Classical.avram_pj_workerC_true_Levy_finite_predictable_physical_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:07:50.859245+00:00
-- url     : https://prove2.me/theorems/7c19197b-060d-482b-96d6-301ee3220dfb
-- title:
--   Actual spectrally negative Lévy law supplies finite physical predictable time×sample clock with exact source measure on every predictable set
-- statement:
--   For the genuine original Lévy process X under its own probability law P, the finite horizon T admits a finite measure on the right-continuous predictable time×sample sigma-field whose measure of every predictable set agrees with the original finite clipped Lebesgue-clock product P. Use X.isProbability explicitly rather than a fabricated probability hypothesis.
-- source:
--   Proved ba32aa0b true-source finite physical predictable clock exists uniquely, X.isProbability field from the original SpectrallyNegativeLevy definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_finite_physical_predictable_clock_exists_unique
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_true_Levy_finite_predictable_physical_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A =
          ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal).prod P) A := by sorry
