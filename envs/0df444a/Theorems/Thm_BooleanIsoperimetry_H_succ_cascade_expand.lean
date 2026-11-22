-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_succ_cascade_expand
-- name    : BooleanIsoperimetry.H_succ_cascade_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:20.116256+00:00
-- url     : https://prove2.me/theorems/009a3d9f-3343-4530-9a51-60a63e97afbe
-- title:
--   Boolean Isoperimetry: H succ cascade expand
-- statement:
--   The Boolean Isoperimetry construction uses the H succ cascade expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L442-L447
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L442-L447

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

theorem BooleanIsoperimetry.H_succ_cascade_expand {n x x0 x1 : ℕ} (hx : CascadeSplit n x x0 x1) (hx0 : x0 ≤ 2 ^ n) :
    max (H n x0) x1 + max (H n x1) x0 = H n x0 + if 1 ≤ x1 then H n x1 else x0 := by sorry
