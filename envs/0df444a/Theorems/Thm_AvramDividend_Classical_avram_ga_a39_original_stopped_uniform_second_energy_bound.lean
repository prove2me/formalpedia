-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a39_original_stopped_uniform_second_energy_bound
-- name    : AvramDividend.Classical.avram_ga_a39_original_stopped_uniform_second_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:18:59.326836+00:00
-- url     : https://prove2.me/theorems/acaca8a7-bdf2-4ebe-8133-1cfe6269a2ee
-- title:
--   Original stopped Gaussian uniform physical grid has expected squared source increment energy bounded by horizon times sigma squared
-- statement:
--   For all uniform physical-grid refinements of the original no-jump Levy process and arbitrary random stopping clock, the expected total squared centred Gaussian increment energy over cells before the clock never exceeds horizon times the source variance rate.
-- source:
--   Quantified original Gaussian positive-only stopped spatial Taylor L1 energy input for b0d9951c using a37 and a38.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a39_original_stopped_uniform_second_energy_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : ∀ m, (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1))
    (ρ : Ω → ℝ≥0)
    (hMeas : ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range m →
      Measurable (fun ω : Ω =>
        X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
          X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c)) :
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
        X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    ∀ m : ℕ,
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal ((Z m i ω) ^ 2) else 0 ∂P) ≤
        ENNReal.ofReal ((n : ℝ) * X.σ ^ 2) := by sorry
