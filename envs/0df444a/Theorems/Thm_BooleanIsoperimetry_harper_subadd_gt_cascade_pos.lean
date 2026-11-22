-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_subadd_gt_cascade_pos
-- name    : BooleanIsoperimetry.harper_subadd_gt_cascade_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:39.26346+00:00
-- url     : https://prove2.me/theorems/45ce5984-ce1a-45c0-a658-225b05350ee5
-- title:
--   Boolean Isoperimetry: harper subadd gt cascade pos
-- statement:
--   The Boolean Isoperimetry construction uses the harper subadd gt cascade pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1816-L1852
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1816-L1852

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

theorem BooleanIsoperimetry.harper_subadd_gt_cascade_pos
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a) (hcase : H n b < a)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    H n p + H n q ≤ H n a + a := by sorry
