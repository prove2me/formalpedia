-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_finite_disjoint_singleton_partition_occupied_card_20261116
-- name    : AvramDividend.Classical.avram_a26_finite_disjoint_singleton_partition_occupied_card_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:01:58.736263+00:00
-- url     : https://prove2.me/theorems/99eb0edd-7d8c-468e-8934-acb65332d80b
-- title:
--   Disjoint finite singleton cells count equals occupied-cell count
-- statement:
--   For a finite family of disjoint finite subsets, if each subset has at most one element, the union cardinal equals the number of nonempty subsets. This is the exact deterministic counting principle for converting the original finite marked-jump time set into the occupied-cell count outside the physical multiple-jump event; use card_biUnion and card_filter.
-- source:
--   Finite partition combinatorics; Mathlib Finset.card_biUnion and Finset.card_filter, pinned revision.

import Mathlib
open Finset Set
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_finite_disjoint_singleton_partition_occupied_card_20261116
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset α)
    (hDisjoint : (I : Set ι).PairwiseDisjoint F)
    (hSingle : ∀ i ∈ I, (F i).card ≤ 1) :
    (I.biUnion F).card =
      (I.filter (fun i => (F i).Nonempty)).card := by sorry
