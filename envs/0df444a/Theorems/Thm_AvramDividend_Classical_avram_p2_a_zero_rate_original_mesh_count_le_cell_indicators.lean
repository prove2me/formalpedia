-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mesh_count_le_cell_indicators
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_mesh_count_le_cell_indicators
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:33:41.297689+00:00
-- url     : https://prove2.me/theorems/9fbc018c-ecc2-4eb7-ac89-908b65084f7e
-- title:
--   Actual original Levy negative mesh-count bounded by source-cell event indicators
-- statement:
--   For the actual original spectrally negative Levy process on its given Ω/P/filtration, the number of distinct right-grid endpoints exhibiting a downward increment below -ε/2 is bounded pointwise by the ENNReal sum of the same negative-increment indicators over original source-cell indices. This is a precise deterministic bridge from the pathwise mesh-liminf theorem to the Proved stationary independent-increment grid mean and L2 bounds, without assuming jump intensity, a compensator, Poisson structure or rate equality. It preserves the exact T/(n+1) original time mesh.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_image_count_le_indicator_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_predecessor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_mesh_count_le_cell_indicators
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ) : ℝ≥0∞) ≤
    ∑ j ∈ Finset.range (n + 1),
      ({v : Ω | X.X (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) v -
        X.X ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) v < -ε / 2}).indicator
        (fun _ : Ω => (1 : ℝ≥0∞)) ω := by sorry
