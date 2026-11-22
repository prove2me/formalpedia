-- Prove2me | Theorems.Thm_Egrs75_P4_not_strictGood_of_lt_leastGoodAbove
-- name    : Egrs75.P4.not_strictGood_of_lt_leastGoodAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:50.122515+00:00
-- url     : https://prove2.me/theorems/2394cdb3-d7f2-43d7-8c0d-5eefc03abfc2
-- title:
--   P4: not strict Good of lt least Good Above
-- statement:
--   **Minimality (KERNEL-CLEAN).**  No index strictly between `j` and `leastGoodAbove` is
--   strictly good: any `k` with `j < k < leastGoodAbove` has `(q-1)/2 < n / q^k % q` — wait,
--   this is `¬ StrictGoodAt`, i.e. the digit is `≥ B`.  Combined with `digit_good_above_top`
--   (`≤ B`) this pins the middle digits to exactly `B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L198-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L198-L204

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

theorem Egrs75.P4.not_strictGood_of_lt_leastGoodAbove {q n k : ℕ} (hq : 3 ≤ q)
    (hbad : 0 < badCountQ q n) (hjk : topBadIndex q n < k)
    (hk : k < leastGoodAbove hq hbad) : ¬ StrictGoodAt q k n := by sorry
