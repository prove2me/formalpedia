-- Prove2me | Theorems.Thm_BooleanIsoperimetry_exists_downMap_ne_of_ne
-- name    : BooleanIsoperimetry.exists_downMap_ne_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:58.570021+00:00
-- url     : https://prove2.me/theorems/a150b681-e1b2-4015-a1c9-ea11d83f23a6
-- title:
--   Boolean Isoperimetry: exists down Map ne of ne
-- statement:
--   If a coordinate Down-compression actually changes the family, it strictly
--   moves at least one vertex down.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L543-L549
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L543-L549

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

theorem BooleanIsoperimetry.exists_downMap_ne_of_ne {N : ℕ} (i : Fin N) (A : Finset (Cube N))
    (hne : coordinateDown i A ≠ A) : ∃ x ∈ A, downMap i A x ≠ x := by sorry
