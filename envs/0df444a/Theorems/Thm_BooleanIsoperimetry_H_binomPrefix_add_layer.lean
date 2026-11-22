-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_binomPrefix_add_layer
-- name    : BooleanIsoperimetry.H_binomPrefix_add_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:17.694324+00:00
-- url     : https://prove2.me/theorems/d8e237df-9c2c-4ac7-906d-d3bfea35c3a4
-- title:
--   Boolean Isoperimetry: H binom Prefix add layer
-- statement:
--   Additive full-layer form of `H_binomPrefix_succ_diff`.  This avoids truncated
--   subtraction and is the shape needed when comparing sums of whole
--   Kruskal-Katona/Macaulay layers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L711-L715
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L711-L715

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

theorem BooleanIsoperimetry.H_binomPrefix_add_layer (n r : ℕ) (hr : 1 ≤ r) :
    H n (binomPrefix n r) + Nat.choose n (r + 1) =
      H n (binomPrefix n (r + 1)) := by sorry
