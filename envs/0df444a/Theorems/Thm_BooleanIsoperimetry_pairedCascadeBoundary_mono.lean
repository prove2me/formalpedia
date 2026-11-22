-- Prove2me | Theorems.Thm_BooleanIsoperimetry_pairedCascadeBoundary_mono
-- name    : BooleanIsoperimetry.pairedCascadeBoundary_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:00.891808+00:00
-- url     : https://prove2.me/theorems/dc69d8a8-7087-4378-b86b-0027e10906ee
-- title:
--   Boolean Isoperimetry: paired Cascade Boundary mono
-- statement:
--   Paired version of `cascadeBoundary_mono`, used when comparing the four exposed
--   blocks in a nested cascade profile.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L889-L893
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L889-L893

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

theorem BooleanIsoperimetry.pairedCascadeBoundary_mono {n x0 x1 y0 y1 z0 z1 w0 w1 : ℕ}
    (hx0 : x0 ≤ z0) (hx1 : x1 ≤ z1) (hy0 : y0 ≤ w0) (hy1 : y1 ≤ w1) :
    pairedCascadeBoundary n x0 x1 y0 y1 ≤ pairedCascadeBoundary n z0 z1 w0 w1 := by sorry
