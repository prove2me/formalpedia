-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_macaulay_GT_sum
-- name    : BooleanIsoperimetry.harper_macaulay_GT_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:15.383955+00:00
-- url     : https://prove2.me/theorems/2c33d5c8-a3af-43bb-ba6b-5d571b9f775f
-- title:
--   Boolean Isoperimetry: harper macaulay GT sum
-- statement:
--   Positive-cascade Case-II (GT) sum leaf.  Sorry-free corollary of
--   `harper_macaulay_exchange_step`: the outer `max`s collapse via
--   `canonical_boundaryCost_eq_H_add` (left) and the GT case `H (n+1) b < a`
--   (right, `max (H (n+1) b) a = a`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L853-L867
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L853-L867

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

theorem BooleanIsoperimetry.harper_macaulay_GT_sum (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by sorry
