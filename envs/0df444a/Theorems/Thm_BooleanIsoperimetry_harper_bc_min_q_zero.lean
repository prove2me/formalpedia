-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_bc_min_q_zero
-- name    : BooleanIsoperimetry.harper_bc_min_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:21.082607+00:00
-- url     : https://prove2.me/theorems/c93c2a7d-4e77-4c83-b965-24ec0b7bfe29
-- title:
--   Boolean Isoperimetry: harper bc min q zero
-- statement:
--   The Boolean Isoperimetry construction uses the harper bc min q zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L422-L430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L422-L430

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

theorem BooleanIsoperimetry.harper_bc_min_q_zero (n : ℕ)
    (_ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit n (a + b) p 0) :
    H n p + p ≤ max (H n a) b + max (H n b) a := by sorry
