-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_bc_min_case_le
-- name    : BooleanIsoperimetry.harper_bc_min_case_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:46.296459+00:00
-- url     : https://prove2.me/theorems/4d226bc2-e1b5-478c-ad9f-5207321c58df
-- title:
--   Boolean Isoperimetry: harper bc min case le
-- statement:
--   The Boolean Isoperimetry construction uses the harper bc min case le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1929-L1943
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1929-L1943

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

theorem BooleanIsoperimetry.harper_bc_min_case_le
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a) (hcase : a ≤ H n b)
    (_ : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    H n p + H n q ≤ H n a + H n b := by sorry
