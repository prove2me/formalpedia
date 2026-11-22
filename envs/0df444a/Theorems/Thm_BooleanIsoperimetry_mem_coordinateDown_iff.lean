-- Prove2me | Theorems.Thm_BooleanIsoperimetry_mem_coordinateDown_iff
-- name    : BooleanIsoperimetry.mem_coordinateDown_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:08.0428+00:00
-- url     : https://prove2.me/theorems/699ecf4f-6b99-4704-957e-d8463f51264b
-- title:
--   Boolean Isoperimetry: mem coordinate Down iff
-- statement:
--   Membership characterization of the explicit Down compression, read off directly
--   from `coordinateDown_spec`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L195-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L195-L198

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

theorem BooleanIsoperimetry.mem_coordinateDown_iff {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) :
    x ∈ coordinateDown i A ↔
      (x ∈ A ∧ (i ∉ x ∨ x.erase i ∈ A)) ∨ (i ∉ x ∧ x ∉ A ∧ insert i x ∈ A) := by sorry
