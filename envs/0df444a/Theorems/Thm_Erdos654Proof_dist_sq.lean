-- Prove2me | Theorems.Thm_Erdos654Proof_dist_sq
-- name    : Erdos654Proof.dist_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:37:57.49696+00:00
-- url     : https://prove2.me/theorems/9d10c32a-149b-5bff-899f-372f663d7c29
-- title:
--   Erdos654 Proof: dist sq
-- statement:
--   The Erdos654 Proof construction uses the dist sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L62-L63
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L62-L63

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.dist_sq (P Q : ℝ²) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by sorry
