-- Prove2me | Theorems.Thm_BooleanIsoperimetry_hDist_erase_le_hDist
-- name    : BooleanIsoperimetry.hDist_erase_le_hDist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:11.263463+00:00
-- url     : https://prove2.me/theorems/5397b932-ff93-4b5b-9d5f-fd9eca9ff6d5
-- title:
--   Boolean Isoperimetry: h Dist erase le h Dist
-- statement:
--   The Boolean Isoperimetry construction uses the h Dist erase le h Dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L216-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L216-L223

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

theorem BooleanIsoperimetry.hDist_erase_le_hDist {N : ℕ} (i : Fin N) (x y : Cube N) (h : hDist x y ≤ 1) :
    hDist (x.erase i) (y.erase i) ≤ 1 := by sorry
