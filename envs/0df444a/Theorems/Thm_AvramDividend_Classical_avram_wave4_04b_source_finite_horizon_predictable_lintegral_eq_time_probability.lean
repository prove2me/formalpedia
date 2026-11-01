-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
-- name    : AvramDividend.Classical.avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:46:01.627515+00:00
-- url     : https://prove2.me/theorems/16857b34-c56d-4e6d-9b74-2f2983732092
-- title:
--   Exact finite-horizon original predictable lintegral equals actual Lebesgue time × probability integral
-- statement:
--   For any original spectrally negative Lévy source and finite horizon, there exists a finite measure on its genuine right-continuous predictable sigma algebra that agrees with the horizon-restricted Lebesgue time × original probability measure on all predictable sets and also integrates every predictable measurable nonnegative ENNReal function identically to the actual product measure. This bridges conditional square-energy estimates to real time–probability stochastic integrability without artificial coupling; it constructs no Brownian or Poisson stochastic integral.
-- source:
--   Extends canonically Proved cd6e4008 predictable trim construction, and uses exact pinned Mathlib MeasureTheory.lintegral_trim source header theorem at Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean line 457.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
        Measurable[𝓕.rightCont.predictable] f →
        (∫⁻ p, f p ∂μ) =
          (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P))) := by
  sorry
