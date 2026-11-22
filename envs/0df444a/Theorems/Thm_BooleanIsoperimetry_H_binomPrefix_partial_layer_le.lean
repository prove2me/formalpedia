-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_partial_layer_le
-- name    : BooleanIsoperimetry.H_binomPrefix_partial_layer_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:49.151513+00:00
-- url     : https://prove2.me/theorems/6f3c0ef6-c5ee-4ab8-86b1-2839946f83c8
-- title:
--   Boolean Isoperimetry: H binom Prefix partial layer le
-- statement:
--   Partial-layer upper bound for `H` on complete binomial prefixes.  If only `t`
--   points of the next Macaulay layer are available, with `t` no larger than the
--   whole next layer, then adding `t` to the boundary of the lower full prefix
--   stays below the boundary of the next full prefix.
--
--   This is the inequality form of `H_binomPrefix_add_layer`, useful when a cascade
--   comparison cuts through a layer rather than moving by a whole binomial block.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L739-L743
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L739-L743

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

theorem BooleanIsoperimetry.H_binomPrefix_partial_layer_le (n r t : ℕ) (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose n (r + 1)) :
    H n (binomPrefix n r) + t ≤ H n (binomPrefix n (r + 1)) := by sorry
