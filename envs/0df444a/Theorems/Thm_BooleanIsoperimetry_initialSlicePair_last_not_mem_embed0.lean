-- Prove2me | Theorems.Thm_BooleanIsoperimetry_initialSlicePair_last_not_mem_embed0
-- name    : BooleanIsoperimetry.initialSlicePair_last_not_mem_embed0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:22.542812+00:00
-- url     : https://prove2.me/theorems/b59d78c0-8398-4229-830a-2665b04dcedc
-- title:
--   Boolean Isoperimetry: initial Slice Pair last not mem embed0
-- statement:
--   The Boolean Isoperimetry construction uses the initial Slice Pair last not mem embed0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L628-L630
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L628-L630

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

theorem BooleanIsoperimetry.initialSlicePair_last_not_mem_embed0 {N : ℕ} (x : Cube N) :
    Fin.last N ∉ embed0 x := by sorry
