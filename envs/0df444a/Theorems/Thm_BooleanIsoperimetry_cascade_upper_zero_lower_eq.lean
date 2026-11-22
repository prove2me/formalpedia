-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_upper_zero_lower_eq
-- name    : BooleanIsoperimetry.cascade_upper_zero_lower_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:34.209657+00:00
-- url     : https://prove2.me/theorems/8c365b80-4b5e-41a5-b605-af7c4a685480
-- title:
--   Boolean Isoperimetry: cascade upper zero lower eq
-- statement:
--   In the same situation, the lower slice is the whole split mass.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L611-L615
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L611-L615

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.cascade_upper_zero_lower_eq {n q q0 q1 : ℕ}
    (h : CascadeSplit n q q0 q1) (hq1_zero : q1 = 0) :
    q0 = q := by sorry
