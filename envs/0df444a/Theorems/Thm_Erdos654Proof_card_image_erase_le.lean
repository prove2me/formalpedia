-- Prove2me | Theorems.Thm_Erdos654Proof_card_image_erase_le
-- name    : Erdos654Proof.card_image_erase_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:50:59.3467+00:00
-- url     : https://prove2.me/theorems/1c534110-f6ac-459b-9c77-bdc91bc7c746
-- title:
--   Erdos654 Proof: card image erase le
-- statement:
--   If every point of `S` lies in `B` or `C` and `x ∈ B`, then the distances from `x` to the
--   other points of `S` take at most `#B - 1` values plus the number of distances from `x` to `C`.
--   Stated for any `DecidableEq` instance, so that it applies to `distinctDistancesFrom`.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L244-L260
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L244-L260

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.card_image_erase_le [DecidableEq ℝ²] (S B C : Finset ℝ²) {x : ℝ²}
    (hS : ∀ y ∈ S, y ∈ B ∨ y ∈ C) (hx : x ∈ B) :
    #((S.erase x).image fun y ↦ dist y x) ≤ (#B - 1) + #(C.image fun y ↦ dist y x) := by sorry
