-- Prove2me | Theorems.Thm_BooleanIsoperimetry_coordinateDown_potential_lt_of_ne
-- name    : BooleanIsoperimetry.coordinateDown_potential_lt_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:59.16881+00:00
-- url     : https://prove2.me/theorems/8f60f0c9-440a-4ece-bb6a-b6d6eb9a4f33
-- title:
--   Boolean Isoperimetry: coordinate Down potential lt of ne
-- statement:
--   **Coordinate Down-compression strictly decreases the rank potential when it
--   moves something.**  Combined with the proven size- and boundary-control
--   (`coordinateDown_card_eq`, `coordinateDown_neighborhood_card_le`) this gives any
--   non-Down-fixed family an explicit Frankl–Füredi compression descent witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L555-L565
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L555-L565

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

theorem BooleanIsoperimetry.coordinateDown_potential_lt_of_ne {N : ℕ} (i : Fin N) (A : Finset (Cube N))
    (hne : coordinateDown i A ≠ A) :
    compressionPotential (coordinateDown i A) < compressionPotential A := by sorry
