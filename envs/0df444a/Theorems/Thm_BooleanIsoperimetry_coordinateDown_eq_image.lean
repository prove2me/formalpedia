-- Prove2me | Theorems.Thm_BooleanIsoperimetry_coordinateDown_eq_image
-- name    : BooleanIsoperimetry.coordinateDown_eq_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:53.692021+00:00
-- url     : https://prove2.me/theorems/673d4ccd-f4ee-45ed-9de1-bc3da3350fcb
-- title:
--   Boolean Isoperimetry: coordinate Down eq image
-- statement:
--   `coordinateDown` is the image of the family under `downMap`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L509-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L509-L532

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

theorem BooleanIsoperimetry.coordinateDown_eq_image {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    coordinateDown i A = A.image (downMap i A) := by sorry
