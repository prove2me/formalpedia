-- Prove2me | Theorems.Thm_BooleanIsoperimetry_coordinateUp_mem_of_not_mem
-- name    : BooleanIsoperimetry.coordinateUp_mem_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:33.641609+00:00
-- url     : https://prove2.me/theorems/174b3dd1-1df9-4dde-a11e-55cbd95b3e39
-- title:
--   Boolean Isoperimetry: coordinate Up mem of not mem
-- statement:
--   The Boolean Isoperimetry construction uses the coordinate Up mem of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L185-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L185-L187

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

theorem BooleanIsoperimetry.coordinateUp_mem_of_not_mem {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N)
    (hix : i ∉ x) : x ∈ coordinateUp i A ↔ x ∈ A ∧ insert i x ∈ A := by sorry
