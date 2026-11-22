-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_split_binomPrefix
-- name    : BooleanIsoperimetry.cascade_split_binomPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:14.224069+00:00
-- url     : https://prove2.me/theorems/c222343e-456e-4bec-a7f0-a17f2a110986
-- title:
--   Boolean Isoperimetry: cascade split binom Prefix
-- statement:
--   A full binomial prefix `binomPrefix (n+1) r` splits canonically into the corresponding
--   full layers `binomPrefix n r` and `binomPrefix n (r-1)` in the lower dimensions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L621-L631
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L621-L631

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

theorem BooleanIsoperimetry.cascade_split_binomPrefix (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n + 1) :
    CascadeSplit n (binomPrefix (n + 1) r) (binomPrefix n r) (binomPrefix n (r - 1)) := by sorry
