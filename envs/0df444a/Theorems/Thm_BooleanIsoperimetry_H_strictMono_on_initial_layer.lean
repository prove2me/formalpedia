-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_strictMono_on_initial_layer
-- name    : BooleanIsoperimetry.H_strictMono_on_initial_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:18.086797+00:00
-- url     : https://prove2.me/theorems/24e1c448-817f-4805-87ff-9e6288133eae
-- title:
--   Boolean Isoperimetry: H strict Mono on initial layer
-- statement:
--   Strictness consequence of the increment lower bound: before rank `n`, extending
--   the initial segment by one strictly enlarges its closed neighborhood.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L335-L338
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L335-L338

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

theorem BooleanIsoperimetry.H_strictMono_on_initial_layer {n p : ℕ} (hp : p + 1 ≤ 2 ^ n) (hpn : p < n) :
    H n p < H n (p + 1) := by sorry
