-- Prove2me | Theorems.Thm_BooleanIsoperimetry_hDist_comm
-- name    : BooleanIsoperimetry.hDist_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:07.732681+00:00
-- url     : https://prove2.me/theorems/3f09d9cd-0da8-412d-951e-1feb099ed26d
-- title:
--   Boolean Isoperimetry: h Dist comm
-- statement:
--   The Boolean Isoperimetry construction uses the h Dist comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L210-L211
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L210-L211

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

theorem BooleanIsoperimetry.hDist_comm {N : ℕ} (x y : Cube N) : hDist x y = hDist y x := by sorry
