-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_uniform_grid_image_le_enat_indicator_count
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_uniform_grid_image_le_enat_indicator_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:10.794733+00:00
-- url     : https://prove2.me/theorems/2ed8c1d2-4f28-4dc5-b8b6-ff5c1efa8aa8
-- title:
--   Marked uniform grid image ENat cardinal bounded by original indexed-cell indicators
-- statement:
--   For any real-valued path on NNReal time, the extended-natural cardinal of marked right-endpoint images is bounded by the extended-natural sum of indexed original adjacent-grid negative increment indicators. This is an exact same-path finite combinatorial conversion used before taking the liminf over mesh refinements. It respects all endpoint conventions and introduces no stochastic assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_filter_card_eq_enat_indicator_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_adjacent_duration

open AvramDividend.Classical
open scoped NNReal ENat BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_34dbea70_original_uniform_grid_image_le_enat_indicator_count
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    ((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => Y t - Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℕ∞)
    ≤ ∑ i ∈ Finset.range (n + 1),
        (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
          then (1 : ℕ∞) else 0) := by sorry
