-- Prove2me | Theorems.Thm_Egrs75_P4_one_le_geomQ
-- name    : Egrs75.P4.one_le_geomQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:26.739285+00:00
-- url     : https://prove2.me/theorems/f991b4ea-3b1b-4315-890a-6aa8aada1870
-- title:
--   P4: one le geom Q
-- statement:
--   `1 ≤ G q i` for `i ≥ 1` (the `k=0` term is `1`; KERNEL-CLEAN).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L93-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L93-L97

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

theorem Egrs75.P4.one_le_geomQ {q i : ℕ} (hi : 1 ≤ i) : 1 ≤ geomQ q i := by sorry
