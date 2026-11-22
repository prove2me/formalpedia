-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_partial_window_le
-- name    : BooleanIsoperimetry.H_binomPrefix_partial_window_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:58.342167+00:00
-- url     : https://prove2.me/theorems/7b96a06e-6958-42a4-ace2-6e7b5813d5ec
-- title:
--   Boolean Isoperimetry: H binom Prefix partial window le
-- statement:
--   Partial-window upper bound for `H` on complete binomial prefixes.  Any amount
--   `t` bounded by the total size of the complete layers from `r+1` through `s`
--   can be added to `H` at the lower full prefix without exceeding `H` at the upper
--   full prefix.
--
--   This packages the full-window equality in the one-sided form needed for
--   partial-window majorization and nested-cascade interleaving arguments.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L754-L758
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L754-L758

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

theorem BooleanIsoperimetry.H_binomPrefix_partial_window_le (n r s t : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s)
    (ht : t ≤ (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i)) :
    H n (binomPrefix n r) + t ≤ H n (binomPrefix n s) := by sorry
