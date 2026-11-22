-- Prove2me | Theorems.Thm_BooleanIsoperimetry_coordinateDown_mem_of_not_mem
-- name    : BooleanIsoperimetry.coordinateDown_mem_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:32.959796+00:00
-- url     : https://prove2.me/theorems/aa36e142-f520-4338-97a5-b7122f733ed5
-- title:
--   Boolean Isoperimetry: coordinate Down mem of not mem
-- statement:
--   The Boolean Isoperimetry construction uses the coordinate Down mem of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L204-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L204-L206

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

theorem BooleanIsoperimetry.coordinateDown_mem_of_not_mem {N : ℕ} (i : Fin N) (B : Finset (Cube N)) (x : Cube N)
    (hix : i ∉ x) : x ∈ coordinateDown i B ↔ x ∈ B ∨ insert i x ∈ B := by sorry
