-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_diff
-- name    : BooleanIsoperimetry.H_binomPrefix_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:14.586287+00:00
-- url     : https://prove2.me/theorems/55dcbdad-aa0b-4be4-b601-94eb0b5c1530
-- title:
--   Boolean Isoperimetry: H binom Prefix diff
-- statement:
--   Layer-precise increment behavior away from the empty-prefix edge case: the
--   total increment of `H` across the `r`-th positive binomial layer is exactly its
--   size `Nat.choose n r`. This is required because `H` is not concave across layer
--   boundaries.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L687-L694
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L687-L694

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

theorem BooleanIsoperimetry.H_binomPrefix_diff (n r : ℕ) (hr : 2 ≤ r) :
    H n (binomPrefix n r) - H n (binomPrefix n (r - 1)) = Nat.choose n r := by sorry
