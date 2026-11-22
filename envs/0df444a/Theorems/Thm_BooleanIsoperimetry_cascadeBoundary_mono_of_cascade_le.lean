-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascadeBoundary_mono_of_cascade_le
-- name    : BooleanIsoperimetry.cascadeBoundary_mono_of_cascade_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:00.127054+00:00
-- url     : https://prove2.me/theorems/062293cf-cd2c-46cf-b750-b0cf98e73103
-- title:
--   Boolean Isoperimetry: cascade Boundary mono of cascade le
-- statement:
--   Monotonicity of `cascadeBoundary` along canonical cascade splits.  It packages
--   `cascade_slice_mono` with the local boundary monotonicity above.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L899-L903
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L899-L903

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

theorem BooleanIsoperimetry.cascadeBoundary_mono_of_cascade_le {n x x0 x1 y y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) (hxy : x ≤ y) :
    cascadeBoundary n x0 x1 ≤ cascadeBoundary n y0 y1 := by sorry
