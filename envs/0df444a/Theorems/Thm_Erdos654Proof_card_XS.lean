-- Prove2me | Theorems.Thm_Erdos654Proof_card_XS
-- name    : Erdos654Proof.card_XS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:38:09.727617+00:00
-- url     : https://prove2.me/theorems/fa25cd9d-828f-41b1-afdd-e6f99677fa95
-- title:
--   Erdos654 Proof: card XS
-- statement:
--   The Erdos654 Proof construction uses the card XS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L211-L212
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L211-L212

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.card_XS (m : ℕ) : #(XS m) = 2 * m := by sorry
