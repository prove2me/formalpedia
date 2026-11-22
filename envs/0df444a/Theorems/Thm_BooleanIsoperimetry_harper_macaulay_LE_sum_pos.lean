-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_macaulay_LE_sum_pos
-- name    : BooleanIsoperimetry.harper_macaulay_LE_sum_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:22.609795+00:00
-- url     : https://prove2.me/theorems/1357c443-ddba-4ff9-baa2-7b3f19b9f4ed
-- title:
--   Boolean Isoperimetry: harper macaulay LE sum pos
-- statement:
--   Positive-cascade Case-I (LE) sum leaf.  Sorry-free corollary of
--   `harper_macaulay_exchange_step`: collapse the outer `max`s
--   (`canonical_boundaryCost_eq_H_add` on the left; `b ≤ a ≤ H b` on the right).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L820-L834
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L820-L834

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

theorem BooleanIsoperimetry.harper_macaulay_LE_sum_pos (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by sorry
