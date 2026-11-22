-- Prove2me | Theorems.Thm_BooleanIsoperimetry_eq_erase_of_hDist_le_one_of_mem_of_not_mem
-- name    : BooleanIsoperimetry.eq_erase_of_hDist_le_one_of_mem_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:46.779027+00:00
-- url     : https://prove2.me/theorems/94af40ee-1e10-462f-b9c9-13bf765d045f
-- title:
--   Boolean Isoperimetry: eq erase of h Dist le one of mem of not mem
-- statement:
--   The Boolean Isoperimetry construction uses the eq erase of h Dist le one of mem of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L290-L314
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L290-L314

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

theorem BooleanIsoperimetry.eq_erase_of_hDist_le_one_of_mem_of_not_mem {N : ℕ} {x y : Cube N} {i : Fin N}
    (h : hDist x y ≤ 1) (hix : i ∈ x) (hiy : i ∉ y) : y = x.erase i := by sorry
