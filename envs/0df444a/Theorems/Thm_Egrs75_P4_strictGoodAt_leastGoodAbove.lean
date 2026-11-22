-- Prove2me | Theorems.Thm_Egrs75_P4_strictGoodAt_leastGoodAbove
-- name    : Egrs75.P4.strictGoodAt_leastGoodAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:23.341178+00:00
-- url     : https://prove2.me/theorems/843c2c6e-d44f-430e-93df-bebf9a51c5de
-- title:
--   P4: strict Good At least Good Above
-- statement:
--   `leastGoodAbove` is strictly good (KERNEL-CLEAN).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L190-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L190-L192

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.P4
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV

theorem Egrs75.P4.strictGoodAt_leastGoodAbove {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) :
    StrictGoodAt q (leastGoodAbove hq hbad) n := by sorry
