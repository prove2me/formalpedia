-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_subadd_gt
-- name    : BooleanIsoperimetry.harper_subadd_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:54.846369+00:00
-- url     : https://prove2.me/theorems/52c0d9c1-56ba-4081-8ff2-33324140f283
-- title:
--   Boolean Isoperimetry: harper subadd gt
-- statement:
--   Clean form of Case II of Harper's inductive step.
--
--   Non-circular: mentions only `H` and the lower-dimensional `ih`.  When the larger
--   part `a` exceeds the neighborhood of the smaller part (`H n b < a`), the closed
--   neighborhood of the size-`(a+b)` initial segment in the `(n+1)`-cube is no larger
--   than `H n a + a`.  Via `H_succ_cascade` and `canonical_boundaryCost_eq_H_add`
--   this is exactly `harper_bc_min_case_gt`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1901-L1927
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1901-L1927

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

theorem BooleanIsoperimetry.harper_subadd_gt
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (hb_le_a : b ≤ a) (hcase : H n b < a) :
    H (n + 1) (a + b) ≤ H n a + a := by sorry
