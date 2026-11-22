-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_window
-- name    : BooleanIsoperimetry.H_binomPrefix_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:54.446118+00:00
-- url     : https://prove2.me/theorems/1d40bf31-8862-46e5-be52-a248131cfd09
-- title:
--   Boolean Isoperimetry: H binom Prefix window
-- statement:
--   Additive window form for complete binomial layers: moving `H` from the full
--   prefix below layer `r` to the full prefix below layer `s` adds exactly the
--   whole layers `r+1, ..., s`.  This is a reusable whole-block version of the
--   increment-window profile behind the positive-cascade obstruction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L723-L728
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L723-L728

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

theorem BooleanIsoperimetry.H_binomPrefix_window (n r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    H n (binomPrefix n r) +
        (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) =
      H n (binomPrefix n s) := by sorry
