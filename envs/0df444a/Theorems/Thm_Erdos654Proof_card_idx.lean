-- Prove2me | Theorems.Thm_Erdos654Proof_card_idx
-- name    : Erdos654Proof.card_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:38:11.428082+00:00
-- url     : https://prove2.me/theorems/4618379e-8c50-4901-86e4-138f65feeba6
-- title:
--   Erdos654 Proof: card idx
-- statement:
--   The Erdos654 Proof construction uses the card idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L200-L200
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L200-L200

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.card_idx (m : ℕ) : #(idx m) = 2 * m := by sorry
