-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb41_original_gaussian_quadratic_cell_fourth_moment
-- name    : AvramDividend.Classical.avram_gb41_original_gaussian_quadratic_cell_fourth_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:24:06.129282+00:00
-- url     : https://prove2.me/theorems/c9b5ddf0-9d5b-43d0-b1c8-52338ec8a586
-- title:
--   Original zero-jump Gaussian increments have uniform centred-square fourth moments
-- statement:
--   For the original spectrally negative Levy process with zero Levy measure, the centred intrinsic Gaussian increment over each deterministic mesh cell has a quadratic residual whose second moment is bounded by a constant times the square of the mesh width. Uniformly over cells and uniform grids with a fixed finite horizon, its fourth-moment integral is O((m+1)^(-2)). This isolates the genuinely probabilistic input needed for the predictable weighted finite-cap quadratic-grid estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_gb41_original_gaussian_quadratic_cell_fourth_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (n : ℕ) (hn : 0 < n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range (m + 1) →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : Ω → ℝ := fun ω =>
        (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
          (Δ : ℝ) * X.σ ^ 2
      Integrable (fun ω => (R ω) ^ 2) P ∧
        (∫ ω, (R ω) ^ 2 ∂P) ≤ K / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  sorry
