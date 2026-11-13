-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a37_original_stopped_grid_second_energy
-- name    : AvramDividend.Classical.avram_ga_a37_original_stopped_grid_second_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:15:11.963919+00:00
-- url     : https://prove2.me/theorems/7eae76ca-4ad7-4394-982e-8b97076d1f37
-- title:
--   Original stopped Gaussian finite physical grid has bounded expected centred quadratic energy
-- statement:
--   For the genuine original zero-jump Levy process, the expected energy of centred Gaussian increments over physical cells that start before any random stopping clock is bounded by the unconditional Gaussian interval variance budget.
-- source:
--   Positive-only original stopped C2 Taylor b0d9951c small-cell L1 energy bound from original Gaussian second moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a37_original_stopped_grid_second_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c)) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∫⁻ ω, ∑ i ∈ S,
      if s i < ρ ω then ENNReal.ofReal ((Z i ω) ^ 2) else 0 ∂P) ≤
      ∑ _i ∈ S, ENNReal.ofReal ((Δ : ℝ) * X.σ ^ 2) := by sorry
