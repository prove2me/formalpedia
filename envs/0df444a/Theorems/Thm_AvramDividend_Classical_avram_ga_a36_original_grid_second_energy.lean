-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a36_original_grid_second_energy
-- name    : AvramDividend.Classical.avram_ga_a36_original_grid_second_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:14:13.993636+00:00
-- url     : https://prove2.me/theorems/a6a427cf-77e6-4001-b95b-a32005c4a296
-- title:
--   Original no-jump Gaussian centred finite-grid expected quadratic energy is at most time width times volatility squared
-- statement:
--   For any finite family of deterministic intervals on the original no-jump Levy process, the expected sum of squared centred increments is bounded by the sum of their Gaussian variance durations.
-- source:
--   Original stopped Gaussian positive-only Taylor small-increment energy input for b0d9951c; uses Proved original source stopped variance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a36_original_grid_second_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c)) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω) ^ 2) ∂P) ≤
      ∑ _i ∈ S, ENNReal.ofReal ((Δ : ℝ) * X.σ ^ 2) := by sorry
