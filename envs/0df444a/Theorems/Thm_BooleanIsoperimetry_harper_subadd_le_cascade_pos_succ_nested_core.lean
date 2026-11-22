-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_subadd_le_cascade_pos_succ_nested_core
-- name    : BooleanIsoperimetry.harper_subadd_le_cascade_pos_succ_nested_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:34.010718+00:00
-- url     : https://prove2.me/theorems/38e8adbc-bc0b-42b9-acbb-291b338bed68
-- title:
--   Boolean Isoperimetry: harper subadd le cascade pos succ nested core
-- statement:
--   The Boolean Isoperimetry construction uses the harper subadd le cascade pos succ nested core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1644-L1678
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1644-L1678

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.harper_subadd_le_cascade_pos_succ_nested_core
    (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : a ≤ H n b0 + if 1 ≤ b1 then H n b1 else b0)
    (hpq : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (_ : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (_ : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (_ : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (_ : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    H n p0 + (if 1 ≤ p1 then H n p1 else p0) +
        (H n q0 + (if 1 ≤ q1 then H n q1 else q0)) ≤
      H n a0 + (if 1 ≤ a1 then H n a1 else a0) +
        (H n b0 + (if 1 ≤ b1 then H n b1 else b0)) := by sorry
