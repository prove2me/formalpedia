-- Prove2me | Theorems.Thm_Erdos1063_carry_iff
-- name    : Erdos1063.carry_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:43.764455+00:00
-- url     : https://prove2.me/theorems/6f4ac4eb-34c2-5d77-b913-8df5309bd75f
-- title:
--   Erdos1063: carry iff
-- statement:
--   Kummer's carry condition, restated as `n % q < k % q`.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L60-L74
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L60-L74

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.carry_iff {n k q : ℕ} (hq : 0 < q) (hkn : k ≤ n) :
    q ≤ k % q + (n - k) % q ↔ n % q < k % q := by sorry
