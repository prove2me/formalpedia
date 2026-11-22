-- Prove2me | Theorems.Thm_Egrs75_P4_geomQ_mul
-- name    : Egrs75.P4.geomQ_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:15.888514+00:00
-- url     : https://prove2.me/theorems/67533817-a32f-4d9e-a570-acc1e7e15345
-- title:
--   P4: geom Q mul
-- statement:
--   `(q-1)·G q i = q^i - 1` (KERNEL-CLEAN corollary).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L84-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L84-L86

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

theorem Egrs75.P4.geomQ_mul {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    (q - 1) * geomQ q i = q ^ i - 1 := by sorry
