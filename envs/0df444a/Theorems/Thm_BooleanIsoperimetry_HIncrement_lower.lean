-- Prove2me | Theorems.Thm_BooleanIsoperimetry_HIncrement_lower
-- name    : BooleanIsoperimetry.HIncrement_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:19.691343+00:00
-- url     : https://prove2.me/theorems/c6067447-fd7f-4ae8-a27b-b35db7363011
-- title:
--   Boolean Isoperimetry: HIncrement lower
-- statement:
--   First-difference form of `H_increment_lower`: as long as `p + 1` is inside the
--   `n`-cube, the `p`-th increment of `H n` is at least `n - p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L70-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L70-L75

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

theorem BooleanIsoperimetry.HIncrement_lower (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    n - p ≤ HIncrement n p := by sorry
