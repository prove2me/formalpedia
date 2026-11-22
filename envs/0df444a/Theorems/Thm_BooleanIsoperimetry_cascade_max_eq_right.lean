-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_max_eq_right
-- name    : BooleanIsoperimetry.cascade_max_eq_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:09.181094+00:00
-- url     : https://prove2.me/theorems/762a473c-a070-4019-8bd7-ee3c792d72ef
-- title:
--   Boolean Isoperimetry: cascade max eq right
-- statement:
--   The Boolean Isoperimetry construction uses the cascade max eq right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L432-L440
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L432-L440

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

theorem BooleanIsoperimetry.cascade_max_eq_right {n x x0 x1 : ℕ} (hx : CascadeSplit n x x0 x1) :
    max (H n x1) x0 = if 1 ≤ x1 then H n x1 else x0 := by sorry
