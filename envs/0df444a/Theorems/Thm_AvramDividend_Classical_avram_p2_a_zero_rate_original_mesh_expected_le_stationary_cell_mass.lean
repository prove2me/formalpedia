-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mesh_expected_le_stationary_cell_mass
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_mesh_expected_le_stationary_cell_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:41:46.773794+00:00
-- url     : https://prove2.me/theorems/c7ef59f5-2bc8-4d65-be26-4b26c6da03fb
-- title:
--   Original negative uniform-grid expected count bounded by stationary source increment probability sum
-- statement:
--   For the original spectrally negative Levy process at time origin zero and each exact uniform mesh T/(n+1), bound the expected number of distinct grid endpoints with increments below -ε/2 by a finite sum of original single-cell probabilities. This combines the unconditional Proved original-process image-mesh pointwise bound with the Proved stationary finite-grid marked first-moment theorem, preserving the original Ω/P, actual X and exact ENNReal equality. No jump measure rate, compensator, independent model or Poisson conclusion enters.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mesh_count_le_cell_indicators
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_mesh_expected_le_stationary_cell_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    (∫⁻ ω, (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ) : ℝ≥0∞) ∂P) ≤
    ∑ j ∈ Finset.range (n + 1),
      P {v : Ω |
        X.X ((((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) v ∈ Iio (-ε / 2)} := by sorry
