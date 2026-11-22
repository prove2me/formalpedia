-- Prove2me | Theorems.Thm_BooleanIsoperimetry_mem_coordinateUp_iff
-- name    : BooleanIsoperimetry.mem_coordinateUp_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:07.699812+00:00
-- url     : https://prove2.me/theorems/99700680-b697-471d-8ded-040dff9026d1
-- title:
--   Boolean Isoperimetry: mem coordinate Up iff
-- statement:
--   Membership characterization of the explicit Up compression, read off directly
--   from `coordinateUp_spec`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L180-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L180-L183

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

theorem BooleanIsoperimetry.mem_coordinateUp_iff {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) :
    x ∈ coordinateUp i A ↔
      (x ∈ A ∧ (i ∈ x ∨ insert i x ∈ A)) ∨ (i ∈ x ∧ x ∉ A ∧ x.erase i ∈ A) := by sorry
