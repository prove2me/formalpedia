-- Prove2me | Theorems.Thm_Erdos1063_cambie_good
-- name    : Erdos1063.cambie_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:39:27.561619+00:00
-- url     : https://prove2.me/theorems/743dd76e-a3fb-58d0-bb99-4540ccb77f02
-- title:
--   Erdos1063: cambie good
-- statement:
--   In Cambie's witness `m = k * lcm(1, …, k-1)`, every `m - i` with `1 ≤ i < k`
--   divides `m.choose k`.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L430-L517
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L430-L517

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.cambie_good {k i : ℕ} (hk : 3 ≤ k) (hi1 : 1 ≤ i) (hik : i < k) :
    (k * (Finset.Icc 1 (k - 1)).lcm id - i) ∣ (k * (Finset.Icc 1 (k - 1)).lcm id).choose k := by sorry
