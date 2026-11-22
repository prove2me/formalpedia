-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_subadd_le
-- name    : BooleanIsoperimetry.harper_subadd_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:43.445965+00:00
-- url     : https://prove2.me/theorems/d9210514-78bb-4180-aadf-9ab95b07f181
-- title:
--   Boolean Isoperimetry: harper subadd le
-- statement:
--   Clean subadditivity form of Case I of Harper's inductive step.
--
--   This is the genuine combinatorial content (non-circular: it mentions only `H`
--   and the lower-dimensional induction hypothesis `ih`).  It says that when the
--   larger part `a` already fits inside the neighborhood of the smaller part
--   (`a ≤ H n b`), the closed neighborhood of the initial segment of size `a + b`
--   in the `(n+1)`-cube is no larger than `H n a + H n b`.  Via `H_succ_cascade` and
--   `canonical_boundaryCost_eq_H_add` this is exactly `harper_bc_min_case_le`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1864-L1890
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1864-L1890

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

theorem BooleanIsoperimetry.harper_subadd_le
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (hb_le_a : b ≤ a) (hcase : a ≤ H n b) :
    H (n + 1) (a + b) ≤ H n a + H n b := by sorry
