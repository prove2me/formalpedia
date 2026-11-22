-- Prove2me | Theorems.Thm_BooleanIsoperimetry_eq_insert_of_hDist_le_one_of_not_mem_of_mem
-- name    : BooleanIsoperimetry.eq_insert_of_hDist_le_one_of_not_mem_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:42.727802+00:00
-- url     : https://prove2.me/theorems/208e48c8-748e-417d-99ee-a10e2e9c742c
-- title:
--   Boolean Isoperimetry: eq insert of h Dist le one of not mem of mem
-- statement:
--   The Boolean Isoperimetry construction uses the eq insert of h Dist le one of not mem of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L264-L288
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L264-L288

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

theorem BooleanIsoperimetry.eq_insert_of_hDist_le_one_of_not_mem_of_mem {N : ℕ} {x y : Cube N} {i : Fin N}
    (h : hDist x y ≤ 1) (hix : i ∉ x) (hiy : i ∈ y) : y = insert i x := by sorry
