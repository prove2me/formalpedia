-- Prove2me | Theorems.Thm_Erdos654Proof_card_image_dist_le
-- name    : Erdos654Proof.card_image_dist_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:51:18.821976+00:00
-- url     : https://prove2.me/theorems/1d79df3a-4a69-4128-b08d-f854144606d5
-- title:
--   Erdos654 Proof: card image dist le
-- statement:
--   The distances from `x` to the points `f q`, `q ∈ idx m`, take at most `m` values when they
--   depend only on the second component of `q`.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L269-L283
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L269-L283

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.card_image_dist_le (m : ℕ) (f : Bool × ℕ → ℝ²) (x : ℝ²)
    (hf : ∀ q, dist (f q) x = dist (f (true, q.2)) x) :
    #(((idx m).image f).image fun y ↦ dist y x) ≤ m := by sorry
