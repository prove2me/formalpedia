-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_uniform_grid_image_le_indicator_count
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_uniform_grid_image_le_indicator_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:24:32.625164+00:00
-- url     : https://prove2.me/theorems/44aa4a7e-e258-4f6f-9b1f-170371690a70
-- title:
--   Marked uniform image endpoints have no more elements than corresponding grid indicator sum
-- statement:
--   For an arbitrary real-valued path Y on NNReal time, any uniform grid T/(n+1), and any real threshold epsilon, the ENNReal cardinal of marked image endpoints whose backward-cell increments are below -epsilon/2 is at most the ENNReal sum of the exact original adjacent-index cell indicators with the same threshold. It is an entirely deterministic finite-grid link between the proved pathwise jump liminf and the source original Lévy stationary expected grid count.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_adjacent_duration

open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_34dbea70_original_uniform_grid_image_le_indicator_count
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    ((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => Y t - Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℝ≥0∞)
    ≤ ∑ i ∈ Finset.range (n + 1),
        (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
          then (1 : ℝ≥0∞) else 0) := by sorry
