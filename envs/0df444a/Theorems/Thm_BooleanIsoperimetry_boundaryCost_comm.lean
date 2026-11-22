-- Prove2me | Theorems.Thm_BooleanIsoperimetry_boundaryCost_comm
-- name    : BooleanIsoperimetry.boundaryCost_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:16.129942+00:00
-- url     : https://prove2.me/theorems/d28995f1-3522-4aff-ad55-9091c3879eec
-- title:
--   Boolean Isoperimetry: boundary Cost comm
-- statement:
--   The Boolean Isoperimetry construction uses the boundary Cost comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L376-L379
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L376-L379

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

theorem BooleanIsoperimetry.boundaryCost_comm (n a b : ℕ) :
    max (H n a) b + max (H n b) a =
    max (H n b) a + max (H n a) b := by sorry
