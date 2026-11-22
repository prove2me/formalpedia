-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_coordinateUp_subset
-- name    : BooleanIsoperimetry.neighborhood_coordinateUp_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:46.272574+00:00
-- url     : https://prove2.me/theorems/8edea1fc-2172-4252-9390-b5a8ab9f2bb1
-- title:
--   Boolean Isoperimetry: neighborhood coordinate Up subset
-- statement:
--   **Coordinate Up shadow inclusion (PDF Frankl-Füredi).**  The closed unit
--   neighborhood of an Up-compressed family is contained in the Up-compression of the
--   neighborhood.  This is the classical "compression does not expand the shadow" fact.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L319-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L319-L350

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

theorem BooleanIsoperimetry.neighborhood_coordinateUp_subset {N : ℕ} {i : Fin N} {A : Finset (Cube N)} :
    neighborhood 1 (coordinateUp i A) ⊆ coordinateUp i (neighborhood 1 A) := by sorry
