-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_uniform_original_grid_mean_stationary_cells
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_uniform_original_grid_mean_stationary_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:52:35.671178+00:00
-- url     : https://prove2.me/theorems/5da29be4-e1a4-4554-b549-18ca9017cfdb
-- title:
--   Original Lévy uniform-grid marked mean equals a sum of equal one-time probabilities
-- statement:
--   For the actual original Lévy X on the unchanged probability space and any Borel mark set B, the expectation of the finite uniform grid marked-increment indicator sum over (0,T] equals the sum of n+1 identical original source probabilities P(X_{T/(n+1)} in B). Uses the proved exact stationary-increment finite-grid mean result and the actual NNReal uniform adjacent-grid duration identity. No Lévy-rate, compensator or replacement-process assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_adjacent_duration

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_uniform_original_grid_mean_stationary_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
      B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
        (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
          X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
    ∑ _i ∈ Finset.range (n + 1),
      P {ω : Ω | X.X (T / ((n : ℝ≥0) + 1)) ω ∈ B} := by sorry
