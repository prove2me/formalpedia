-- Prove2me | Theorems.Thm_Erdos654Proof_dist_xpt
-- name    : Erdos654Proof.dist_xpt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:51:27.413561+00:00
-- url     : https://prove2.me/theorems/9e5b8176-5a10-5ae8-ab5b-e1929670b6a9
-- title:
--   Erdos654 Proof: dist xpt
-- statement:
--   The Erdos654 Proof construction uses the dist xpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L295-L301
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L295-L301

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.dist_xpt (p q : Bool × ℕ) : dist (xpt q) (ypt p) = dist (xpt (true, q.2)) (ypt p) := by sorry
