-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_slice_mono
-- name    : BooleanIsoperimetry.cascade_slice_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:14.434806+00:00
-- url     : https://prove2.me/theorems/fd119cb1-e58e-4c52-9fd4-b7b898f4e1b3
-- title:
--   Boolean Isoperimetry: cascade slice mono
-- statement:
--   Monotonicity of the canonical cascade slices.  If `x ≤ y` then both canonical
--   slice values of `x` are dominated by those of `y`.  This is because the lower
--   (resp. upper) slice of a simplicial initial segment is monotone in the segment
--   size (initial segments are nested), and `slice_card_eq_cascade` identifies these
--   slice cardinalities with the cascade split values.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L524-L541
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L524-L541

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

theorem BooleanIsoperimetry.cascade_slice_mono {n x x0 x1 y y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) (hxy : x ≤ y) :
    x0 ≤ y0 ∧ x1 ≤ y1 := by sorry
