-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_weighted_indicator_finset_sum
-- name    : AvramDividend.Classical.avram_p2_l_mesh_weighted_indicator_finset_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:40:23.591937+00:00
-- url     : https://prove2.me/theorems/78024fad-988b-4728-b11a-d7ecc66df42a
-- title:
--   Finite weighted mark indicator sum equals a filter-cardinality multiple
-- statement:
--   The real sum of a common weight over finitely many marked elements is their finite marked count times that weight; supports source-faithful original cadlag grid and intrinsic finite simple-test decomposition.

import Mathlib

open Set Filter Topology
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_weighted_indicator_finset_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (v : α → ℝ) (B : Set ℝ) (c : ℝ) :
    (∑ x ∈ s, if v x ∈ B then c else 0) =
      ((s.filter (fun x => v x ∈ B)).card : ℝ) * c := by sorry
