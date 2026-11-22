-- Prove2me | Theorems.Thm_BooleanIsoperimetry_pairedCascadeBoundary_eq_H_add
-- name    : BooleanIsoperimetry.pairedCascadeBoundary_eq_H_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:59.956249+00:00
-- url     : https://prove2.me/theorems/e73a9c6a-61a2-4019-ac3d-628b5d2496ba
-- title:
--   Boolean Isoperimetry: paired Cascade Boundary eq H add
-- statement:
--   Paired nested boundaries rewrite to the sum of the two `H (n+1)` boundary
--   values.  This packages the four-block expression that occurs in the two open
--   positive-cascade leaves.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L868-L872
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L868-L872

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

theorem BooleanIsoperimetry.pairedCascadeBoundary_eq_H_add {n x y x0 x1 y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) :
    pairedCascadeBoundary n x0 x1 y0 y1 = H (n + 1) x + H (n + 1) y := by sorry
