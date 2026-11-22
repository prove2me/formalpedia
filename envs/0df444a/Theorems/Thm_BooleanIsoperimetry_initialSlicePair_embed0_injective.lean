-- Prove2me | Theorems.Thm_BooleanIsoperimetry_initialSlicePair_embed0_injective
-- name    : BooleanIsoperimetry.initialSlicePair_embed0_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:58.222527+00:00
-- url     : https://prove2.me/theorems/ac7de46b-9425-40e7-90d0-2a1007831222
-- title:
--   Boolean Isoperimetry: initial Slice Pair embed0 injective
-- statement:
--   The Boolean Isoperimetry construction uses the initial Slice Pair embed0 injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L625-L626
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L625-L626

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

theorem BooleanIsoperimetry.initialSlicePair_embed0_injective {N : ℕ} : Function.Injective (@embed0 N) := by sorry
