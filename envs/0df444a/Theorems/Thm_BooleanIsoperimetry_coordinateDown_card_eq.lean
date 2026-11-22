-- Prove2me | Theorems.Thm_BooleanIsoperimetry_coordinateDown_card_eq
-- name    : BooleanIsoperimetry.coordinateDown_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:33.73973+00:00
-- url     : https://prove2.me/theorems/042467d4-36ee-4c43-9a3c-bdc4a1641ad7
-- title:
--   Boolean Isoperimetry: coordinate Down card eq
-- statement:
--   The Boolean Isoperimetry construction uses the coordinate Down card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L418-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L418-L421

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

theorem BooleanIsoperimetry.coordinateDown_card_eq {N : ℕ} {i : Fin N} {B B' : Finset (Cube N)}
    (hB : IsCoordinateDown i B B') :
    B'.card = B.card := by sorry
