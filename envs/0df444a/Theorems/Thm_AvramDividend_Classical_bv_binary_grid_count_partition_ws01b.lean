-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_binary_grid_count_partition_ws01b
-- name    : AvramDividend.Classical.bv_binary_grid_count_partition_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:20:07.316699+00:00
-- url     : https://prove2.me/theorems/6686b98d-7ca4-47f8-ae07-8853edb3419d
-- title:
--   Exact partition of binary sample paths into unique fixed-cardinality active grid patterns
-- statement:
--   For any finite grid with disjoint active and inactive cell predicates, the set of samples for which every cell is classified and exactly k cells are active is precisely the set of samples admitting a k-element subset of the grid that specifies all active/inactive outcomes. The active subset is unique, and no measurability or stochastic assumptions are needed for this set identity.
-- source:
--   The complete proof passed the pinned remote Prove2Me Lean compiler on 28 October 2026. Define the active subset by Finset.filter; derive its powersetCard membership from the active count, and prove conversely that any admissible pattern determines exactly the filter set, using the disjointness hypothesis to exclude conflicting classifications.

import Mathlib

open Set
open scoped BigOperators Classical

/-- Exact finite binary-grid partition: every sample with exactly k active
cells and no third cell outcome has a unique k-element active pattern. -/

theorem AvramDividend.Classical.bv_binary_grid_count_partition_ws01b
    {Ω : Type*} (A B : ℕ → Set Ω) (n k : ℕ)
    (hExcl : ∀ i : ℕ, i < n → ∀ ω : Ω,
      ω ∈ A i → ω ∈ B i → False) :
    {ω : Ω | (∀ i : ℕ, i < n → ω ∈ A i ∨ ω ∈ B i) ∧
      ((Finset.range n).filter (fun i => ω ∈ A i)).card = k} =
    {ω : Ω | ∃ S ∈ Finset.powersetCard k (Finset.range n),
      ∀ i : ℕ, i < n →
        if i ∈ S then ω ∈ A i else ω ∈ B i} := by sorry
