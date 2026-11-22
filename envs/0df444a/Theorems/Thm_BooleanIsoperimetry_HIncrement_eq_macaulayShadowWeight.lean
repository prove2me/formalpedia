-- Prove2me | Theorems.Thm_BooleanIsoperimetry_HIncrement_eq_macaulayShadowWeight
-- name    : BooleanIsoperimetry.HIncrement_eq_macaulayShadowWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:01.061473+00:00
-- url     : https://prove2.me/theorems/30953d3d-0373-4da9-b666-fed3631958c2
-- title:
--   Boolean Isoperimetry: HIncrement eq macaulay Shadow Weight
-- statement:
--   Uniform exact first-difference formula, including the empty vertex.  This is the
--   rank-indexed layer profile used to turn a Macaulay shadow window into an
--   ordinary sum over vertices in the corresponding rank interval.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L213-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L213-L222

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

theorem BooleanIsoperimetry.HIncrement_eq_macaulayShadowWeight {n : ℕ} (p : ℕ) (w : Cube n)
    (hw : rank w = p) :
    HIncrement n p = macaulayShadowWeight w := by sorry
