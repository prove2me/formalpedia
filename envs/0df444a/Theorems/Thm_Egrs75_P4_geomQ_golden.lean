-- Prove2me | Theorems.Thm_Egrs75_P4_geomQ_golden
-- name    : Egrs75.P4.geomQ_golden
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:50.698533+00:00
-- url     : https://prove2.me/theorems/dfbc6111-5784-49af-9470-8d7b3fae00a8
-- title:
--   P4: geom Q golden
-- statement:
--   **GOLDEN identity (KERNEL-CLEAN).**  `(q-1)·G q i + 1 = q^i` for `q ≥ 1`.
--   Division- and subtraction-free form of `G q i = (q^i - 1)/(q - 1)`, from `geom_sum_mul_add`
--   at `x = q-1` (`(q-1)+1 = q`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L75-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L75-L81

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

theorem Egrs75.P4.geomQ_golden {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    (q - 1) * geomQ q i + 1 = q ^ i := by sorry
