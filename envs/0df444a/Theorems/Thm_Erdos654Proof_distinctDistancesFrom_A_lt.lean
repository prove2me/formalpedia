-- Prove2me | Theorems.Thm_Erdos654Proof_distinctDistancesFrom_A_lt
-- name    : Erdos654Proof.distinctDistancesFrom_A_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:51:41.906472+00:00
-- url     : https://prove2.me/theorems/0e418da3-c681-4c65-a01d-c3e3897533ae
-- title:
--   Erdos654 Proof: distinct Distances From A lt
-- statement:
--   Every point of `A m` has at most `3m - 1` distinct distances to the other points.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L304-L321
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L304-L321

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.distinctDistancesFrom_A_lt (m : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ A m, distinctDistancesFrom (A m) x < 3 * m := by sorry
