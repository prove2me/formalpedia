-- Prove2me | Theorems.Thm_BooleanIsoperimetry_initialSlicePair_embed1_injective
-- name    : BooleanIsoperimetry.initialSlicePair_embed1_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:02.738037+00:00
-- url     : https://prove2.me/theorems/16ba6603-630a-4d9f-ba16-1baccf9659fe
-- title:
--   Boolean Isoperimetry: initial Slice Pair embed1 injective
-- statement:
--   The Boolean Isoperimetry construction uses the initial Slice Pair embed1 injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L632-L638
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L632-L638

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

theorem BooleanIsoperimetry.initialSlicePair_embed1_injective {N : ℕ} : Function.Injective (@embed1 N) := by sorry
