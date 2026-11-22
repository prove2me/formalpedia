-- Prove2me | Theorems.Thm_Egrs75_P4_topBad_lt_leastGoodAbove
-- name    : Egrs75.P4.topBad_lt_leastGoodAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:13.681462+00:00
-- url     : https://prove2.me/theorems/42d1ed10-725d-4dbd-8761-bfdf36604990
-- title:
--   P4: top Bad lt least Good Above
-- statement:
--   `leastGoodAbove` lies strictly above the top bad index (KERNEL-CLEAN).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L185-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L185-L187

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

theorem Egrs75.P4.topBad_lt_leastGoodAbove {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) :
    topBadIndex q n < leastGoodAbove hq hbad := by sorry
