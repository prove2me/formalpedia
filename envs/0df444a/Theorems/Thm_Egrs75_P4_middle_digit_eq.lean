-- Prove2me | Theorems.Thm_Egrs75_P4_middle_digit_eq
-- name    : Egrs75.P4.middle_digit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:53.785101+00:00
-- url     : https://prove2.me/theorems/07d7e602-684c-46f3-a894-fee99e0a2004
-- title:
--   P4: middle digit eq
-- statement:
--   **Middle digits are exactly `B` (KERNEL-CLEAN).**  For `j < k < i = leastGoodAbove`,
--   the base-`q` digit of `n` at index `k` equals `(q-1)/2`.  (`digit_good_above_top` gives
--   `≤ B`; non-strict-goodness gives `≥ B`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L209-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L209-L215

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

theorem Egrs75.P4.middle_digit_eq {q n k : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n)
    (hjk : topBadIndex q n < k) (hk : k < leastGoodAbove hq hbad) :
    n / q ^ k % q = (q - 1) / 2 := by sorry
