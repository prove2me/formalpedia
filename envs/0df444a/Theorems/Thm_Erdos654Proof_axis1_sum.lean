-- Prove2me | Theorems.Thm_Erdos654Proof_axis1_sum
-- name    : Erdos654Proof.axis1_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T12:43:25.080621+00:00
-- url     : https://prove2.me/theorems/189295dd-5714-4540-bafe-419a8d4cff10
-- title:
--   Erdos654 Proof: axis1 sum
-- statement:
--   Two distinct points of the second axis at distance `r` from `c` are symmetric about `c 1`.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L88-L98
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L88-L98

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.axis1_sum {P Q c : ℝ²} {r : ℝ} (hP : P 0 = 0) (hQ : Q 0 = 0) (hPQ : P ≠ Q)
    (hPr : dist P c = r) (hQr : dist Q c = r) : P 1 + Q 1 = 2 * c 1 := by sorry
