-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_bc_min_q_zero_core
-- name    : BooleanIsoperimetry.harper_bc_min_q_zero_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:13.650586+00:00
-- url     : https://prove2.me/theorems/e5637cfd-b30f-412d-9397-12435847cfe3
-- title:
--   Boolean Isoperimetry: harper bc min q zero core
-- statement:
--   The Boolean Isoperimetry construction uses the harper bc min q zero core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L399-L420
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L399-L420

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

theorem BooleanIsoperimetry.harper_bc_min_q_zero_core (n : ℕ) {a b p : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit n (a + b) p 0) :
    H n p + p ≤ max (H n a) b + max (H n b) a := by sorry
