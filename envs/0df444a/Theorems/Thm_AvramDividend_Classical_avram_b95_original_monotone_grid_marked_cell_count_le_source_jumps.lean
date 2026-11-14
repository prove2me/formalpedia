-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b95_original_monotone_grid_marked_cell_count_le_source_jumps
-- name    : AvramDividend.Classical.avram_b95_original_monotone_grid_marked_cell_count_le_source_jumps
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:35:30.406535+00:00
-- url     : https://prove2.me/theorems/67fc29c6-7180-474e-9c0d-ec523fbfe5f4
-- title:
--   Marked monotone physical grid cells are bounded by original jump-time count
-- statement:
--   The true original jump times witnessing marked cells of a monotone finite grid admit an injective choice. The proved original grid index uniqueness forbids a single source jump being the witness for two different cells. Therefore the number of marked cells is bounded by the number of original jump times in the finite source set. Used for physical marked-cardinality domination in stopped mixed Levy energy.
-- source:
--   Original wave7_06 monotone marked grid uniqueness and Mathlib Finset.card_le_card_of_injOn.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_monotone_marked_grid_index_unique
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Distinct genuinely marked monotone source grid cells require distinct original source jump times. -/

theorem AvramDividend.Classical.avram_b95_original_monotone_grid_marked_cell_count_le_source_jumps
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (J : Finset ℕ) (F : Finset ℝ≥0)
    (hJ : ∀ i ∈ J, ∃ u ∈ F,
      u ∈ Ioc (grid i) (grid (i + 1))) :
    J.card ≤ F.card := by sorry
