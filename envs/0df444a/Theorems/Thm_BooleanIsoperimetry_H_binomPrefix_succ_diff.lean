-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_succ_diff
-- name    : BooleanIsoperimetry.H_binomPrefix_succ_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:44.296851+00:00
-- url     : https://prove2.me/theorems/9aa7939b-33e8-412e-a394-e52ce7f700f8
-- title:
--   Boolean Isoperimetry: H binom Prefix succ diff
-- statement:
--   Adjacent full-binomial-prefix form of the same layer calculation.  This avoids
--   subtraction from `r - 1` and is often the cleaner statement for induction over
--   cascade layers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L701-L704
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L701-L704

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

theorem BooleanIsoperimetry.H_binomPrefix_succ_diff (n r : ℕ) (hr : 1 ≤ r) :
    H n (binomPrefix n (r + 1)) - H n (binomPrefix n r) =
      Nat.choose n (r + 1) := by sorry
