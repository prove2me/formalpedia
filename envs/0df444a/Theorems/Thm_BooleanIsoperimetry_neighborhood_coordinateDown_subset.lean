-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_coordinateDown_subset
-- name    : BooleanIsoperimetry.neighborhood_coordinateDown_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:48.637118+00:00
-- url     : https://prove2.me/theorems/cd3ae629-8438-4797-85c3-1212d5ff8a90
-- title:
--   Boolean Isoperimetry: neighborhood coordinate Down subset
-- statement:
--   **Coordinate Down shadow inclusion (PDF Frankl-Füredi).**  The mirror of
--   `neighborhood_coordinateUp_subset` for Down compression.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L354-L387
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L354-L387

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

theorem BooleanIsoperimetry.neighborhood_coordinateDown_subset {N : ℕ} {i : Fin N} {A : Finset (Cube N)} :
    neighborhood 1 (coordinateDown i A) ⊆ coordinateDown i (neighborhood 1 A) := by sorry
