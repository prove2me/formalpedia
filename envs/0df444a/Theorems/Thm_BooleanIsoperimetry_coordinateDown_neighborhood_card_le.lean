-- Prove2me | Theorems.Thm_BooleanIsoperimetry_coordinateDown_neighborhood_card_le
-- name    : BooleanIsoperimetry.coordinateDown_neighborhood_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:31.14761+00:00
-- url     : https://prove2.me/theorems/825674cf-3293-4418-8d43-4902372963a2
-- title:
--   Boolean Isoperimetry: coordinate Down neighborhood card le
-- statement:
--   **PDF compression lemma (Down move).**  The mirror of
--   `coordinateUp_neighborhood_card_le`: a Down-compression along coordinate `i` does
--   not increase the closed unit neighborhood, `|N(C_i^↓ B)| ≤ |N(B)|`.  Symmetric to
--   the Up case under the coordinate-`i` flip isometry of the cube.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L444-L450
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L444-L450

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

theorem BooleanIsoperimetry.coordinateDown_neighborhood_card_le {N : ℕ} {i : Fin N} {B B' : Finset (Cube N)}
    (hB : IsCoordinateDown i B B') :
    (neighborhood 1 B').card ≤ (neighborhood 1 B).card := by sorry
