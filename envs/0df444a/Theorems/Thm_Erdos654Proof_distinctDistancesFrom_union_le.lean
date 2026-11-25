-- Prove2me | Theorems.Thm_Erdos654Proof_distinctDistancesFrom_union_le
-- name    : Erdos654Proof.distinctDistancesFrom_union_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:50:55.6442+00:00
-- url     : https://prove2.me/theorems/96e0ad72-abad-5ddb-aff8-bc80c89c07a3
-- title:
--   Erdos654 Proof: distinct Distances From union le
-- statement:
--   The Erdos654 Proof construction uses the distinct Distances From union le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L262-L265
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L262-L265

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.distinctDistancesFrom_union_le (B C : Finset ℝ²) {x : ℝ²} (hx : x ∈ B) :
    distinctDistancesFrom (B ∪ C) x ≤ (#B - 1) + #(C.image fun y ↦ dist y x) := by sorry
