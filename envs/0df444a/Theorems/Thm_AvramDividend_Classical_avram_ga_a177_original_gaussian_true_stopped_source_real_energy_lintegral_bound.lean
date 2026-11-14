-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a177_original_gaussian_true_stopped_source_real_energy_lintegral_bound
-- name    : AvramDividend.Classical.avram_ga_a177_original_gaussian_true_stopped_source_real_energy_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:59:51.792986+00:00
-- url     : https://prove2.me/theorems/a4d216a6-3029-43ce-aa6e-6b753e3094e2
-- title:
--   Original Gaussian stopped full physical source real squared-energy sum has extended nonnegative expectation at most horizon volatility budget
-- statement:
--   Convert the Proved Gaussian source stopped-prefix square-energy bound for a sum of extended nonnegative increments into the exact ENNReal.ofReal of the real-valued finite sum of original source centred squared increments, without changing the actual physical mask or process.
-- source:
--   ga_a39 original Gaussian variance-energy bound; ENNReal.ofReal_sum_of_nonneg and original adapted increments measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a39_original_stopped_uniform_second_energy_bound
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a177_original_gaussian_true_stopped_source_real_energy_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ < ρ ω then
          (X.X ((i : ℝ≥0) * Δ + Δ) ω -
            X.X ((i : ℝ≥0) * Δ) ω - (Δ : ℝ) * X.c)^2
        else 0
    ∀ m : ℕ,
      (∫⁻ ω, ENNReal.ofReal (E m ω) ∂P) ≤
        ENNReal.ofReal ((n : ℝ) * X.σ^2) := by sorry
