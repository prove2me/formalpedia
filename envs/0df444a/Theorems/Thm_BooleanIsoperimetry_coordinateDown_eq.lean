-- Prove2me | Theorems.Thm_BooleanIsoperimetry_coordinateDown_eq
-- name    : BooleanIsoperimetry.coordinateDown_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:28.340143+00:00
-- url     : https://prove2.me/theorems/4ac56a6b-db4e-4baf-ae1e-4b81def0e8f7
-- title:
--   Boolean Isoperimetry: coordinate Down eq
-- statement:
--   The Boolean Isoperimetry construction uses the coordinate Down eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L174-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L174-L176

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

theorem BooleanIsoperimetry.coordinateDown_eq {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateDown i A A') : A' = coordinateDown i A := by sorry
