-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_grid_expectation
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_grid_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:29:50.385842+00:00
-- url     : https://prove2.me/theorems/3c63c970-b4e9-4f60-aae9-0b636f46bb61
-- title:
--   Expected original uniform-grid Borel mark indicators equal source one-time probability times cell count
-- statement:
--   On the genuine original process X and its original probability space Ω/P, the expected sum of Borel marked uniform-grid increments equals the number of cells times the original one-time source probability at the common cell width, as an exact ENNReal equality valid for T=0 and infinite values. This combines the already-Proved original stationary finite-grid first moment and exact uniform source-cell width; it does not identify the event probability with X.ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_grid_probability_sum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_grid_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ∑ j ∈ Finset.range (n + 1),
      B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
        (X.X (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
         X.X ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
    (((n + 1 : ℕ) : ℝ≥0∞) * P {ω : Ω | X.X (T / ((n : ℝ≥0) + 1)) ω ∈ B}) := by sorry
