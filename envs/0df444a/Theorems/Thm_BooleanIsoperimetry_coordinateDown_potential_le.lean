-- Prove2me | Theorems.Thm_BooleanIsoperimetry_coordinateDown_potential_le
-- name    : BooleanIsoperimetry.coordinateDown_potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:03.299562+00:00
-- url     : https://prove2.me/theorems/31cb504b-863b-47e5-90d3-60f24725a3db
-- title:
--   Boolean Isoperimetry: coordinate Down potential le
-- statement:
--   `coordinateDown` never increases the rank potential.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L535-L539
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L535-L539

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.coordinateDown_potential_le {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    compressionPotential (coordinateDown i A) ≤ compressionPotential A := by sorry
