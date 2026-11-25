-- Prove2me | Theorems.Thm_Erdos654Proof_dist_ypt
-- name    : Erdos654Proof.dist_ypt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:51:09.8261+00:00
-- url     : https://prove2.me/theorems/bd758a35-7ae1-569e-80a0-d3c402efee53
-- title:
--   Erdos654 Proof: dist ypt
-- statement:
--   The Erdos654 Proof construction uses the dist ypt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L289-L293
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L289-L293

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.dist_ypt (p q : Bool × ℕ) : dist (ypt q) (xpt p) = dist (ypt (true, q.2)) (xpt p) := by sorry
