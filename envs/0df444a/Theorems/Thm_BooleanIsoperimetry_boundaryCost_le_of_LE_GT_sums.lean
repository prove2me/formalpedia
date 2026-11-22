-- Prove2me | Theorems.Thm_BooleanIsoperimetry_boundaryCost_le_of_LE_GT_sums
-- name    : BooleanIsoperimetry.boundaryCost_le_of_LE_GT_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:15.113904+00:00
-- url     : https://prove2.me/theorems/214f9960-ddd8-4330-ab86-65b5d5c457fe
-- title:
--   Boolean Isoperimetry: boundary Cost le of LE GT sums
-- statement:
--   The Boolean Isoperimetry construction uses the boundary Cost le of LE GT sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L869-L897
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L869-L897

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

theorem BooleanIsoperimetry.boundaryCost_le_of_LE_GT_sums (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (_hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q) (hba : b ≤ a) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by sorry
