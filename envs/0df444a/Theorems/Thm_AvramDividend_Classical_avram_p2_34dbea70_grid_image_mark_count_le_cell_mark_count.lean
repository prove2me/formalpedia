-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
-- name    : AvramDividend.Classical.avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:49:35.597991+00:00
-- url     : https://prove2.me/theorems/69c9f50d-efbc-4edb-b68c-ab37efcb7345
-- title:
--   A marked grid image has no more points than marked source cells
-- statement:
--   For any finite grid index set, endpoint map and mark predicate, filtering the image of grid endpoints has cardinality at most filtering the originating cells by the pulled-back predicate. This deterministic finite combinatorial inequality lets the genuine source pathwise negative-cell liminf be controlled by sums of original increment indicators and subsequently by actual original-process stationary-increment expectations. No stochastic or Lévy-rate hypothesis is assumed.

import Mathlib

open Finset

theorem AvramDividend.Classical.avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
    {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β)
    (marked : β → Prop) [DecidablePred marked] :
    ((s.image f).filter marked).card ≤
      (s.filter (fun x => marked (f x))).card := by sorry
