-- Prove2me | Theorems.Thm_Egrs75_P4_geomQ_succ
-- name    : Egrs75.P4.geomQ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:51.749654+00:00
-- url     : https://prove2.me/theorems/24254a90-45eb-4bd4-b385-116f8e2f6c49
-- title:
--   P4: geom Q succ
-- statement:
--   `G q (i+1) = G q i + q^i` (KERNEL-CLEAN).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L89-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L89-L90

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

theorem Egrs75.P4.geomQ_succ (q i : ℕ) : geomQ q (i + 1) = geomQ q i + q ^ i := by sorry
