-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_nonzero_grid_cells_count_le_selected_jumps
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_finite_nonzero_grid_cells_count_le_selected_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:02:51.044365+00:00
-- url     : https://prove2.me/theorems/9ae88aa9-e4ec-4cc9-8d8c-970c85b4ad5a
-- title:
--   Nonzero grid-test cells are bounded by selected actual jump count
-- statement:
--   If each nonzero entry of a finite uniform grid sum must occur at the index assigned to some member of a finite selected jump set, then the number of nonzero grid cells is at most the number of actual selected jumps. The mapping need not be injective, and the proof requires no probabilistic premise.

import Mathlib

open Set Filter Topology
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_finite_nonzero_grid_cells_count_le_selected_jumps
    {α : Type*} (S : Finset α) (j : α → ℕ)
    (n : ℕ) (g : ℕ → ℝ)
    (hzero : ∀ i ∈ Finset.range (n + 1),
      i ∉ S.image j → g i = 0) :
    ((Finset.range (n + 1)).filter (fun i => g i ≠ 0)).card ≤ S.card := by sorry
