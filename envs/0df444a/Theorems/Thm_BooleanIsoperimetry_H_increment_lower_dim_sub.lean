-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_increment_lower_dim_sub
-- name    : BooleanIsoperimetry.H_increment_lower_dim_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:47.262888+00:00
-- url     : https://prove2.me/theorems/c12df7ec-b384-4e18-9678-850aeb884736
-- title:
--   Boolean Isoperimetry: H increment lower dim sub
-- statement:
--   Additive form of the one-step lower bound: the new point contributes at least
--   `n - p` new neighborhood vertices.  This is a direct corollary of
--   `H_increment_lower`, but the shape is easier to reuse in cascade-layer
--   arguments.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L56-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L56-L64

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

theorem BooleanIsoperimetry.H_increment_lower_dim_sub (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    H n p + (n - p) ≤ H n (p + 1) := by sorry
