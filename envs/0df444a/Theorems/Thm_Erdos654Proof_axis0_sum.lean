-- Prove2me | Theorems.Thm_Erdos654Proof_axis0_sum
-- name    : Erdos654Proof.axis0_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:43:04.157882+00:00
-- url     : https://prove2.me/theorems/1af1393b-bedc-5055-8854-0512743870b5
-- title:
--   Erdos654 Proof: axis0 sum
-- statement:
--   Two distinct points of the first axis at distance `r` from `c` are symmetric about `c 0`.
--
--   Source: https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L75-L85
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean#L75-L85

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof

theorem Erdos654Proof.axis0_sum {P Q c : ℝ²} {r : ℝ} (hP : P 1 = 0) (hQ : Q 1 = 0) (hPQ : P ≠ Q)
    (hPr : dist P c = r) (hQr : dist Q c = r) : P 0 + Q 0 = 2 * c 0 := by sorry
