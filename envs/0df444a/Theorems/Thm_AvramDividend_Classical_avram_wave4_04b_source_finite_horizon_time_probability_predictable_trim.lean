-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
-- name    : AvramDividend.Classical.avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:28:00.094693+00:00
-- url     : https://prove2.me/theorems/cd6e4008-ff64-4f95-991b-6dc636984270
-- title:
--   Finite horizon original Lévy source predictable time probability observation measure
-- statement:
--   For every finite horizon T, the original spectrally negative Lévy source with its actual right-continuous filtration admits a finite measure on the genuine predictable sigma algebra obtained by restricting real Lebesgue measure to [0,T], mapping times to NNReal and taking product with the original probability P, then trimming. On all predictable measurable sets it agrees exactly with the real-time finite horizon time–P product. Requires no value function, dividend control, generator or fictitious stochastic representation.
-- source:
--   Direct extraction and strengthening of finite predictable intensity-budget measure construction already canonically Proved as 6a25e164-a9aa-4694-b8e8-9a47ee895151; removes extraneous value function and control assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A := by
  sorry
