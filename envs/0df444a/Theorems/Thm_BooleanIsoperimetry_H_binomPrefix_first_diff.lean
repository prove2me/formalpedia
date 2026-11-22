-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_first_diff
-- name    : BooleanIsoperimetry.H_binomPrefix_first_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:43.742222+00:00
-- url     : https://prove2.me/theorems/5cc7b804-ff59-43ef-bde2-7433ea89a71f
-- title:
--   Boolean Isoperimetry: H binom Prefix first diff
-- statement:
--   The first full binomial-prefix jump of `H`: the closed neighbourhood of the
--   singleton initial segment contains both the empty layer and the first layer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L675-L679
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L675-L679

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

theorem BooleanIsoperimetry.H_binomPrefix_first_diff (n : ℕ) :
    H n (binomPrefix n 1) - H n (binomPrefix n 0) =
      Nat.choose n 0 + Nat.choose n 1 := by sorry
