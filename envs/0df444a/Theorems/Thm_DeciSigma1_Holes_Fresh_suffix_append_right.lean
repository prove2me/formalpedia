-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_append_right
-- name    : DeciSigma1.Holes.Fresh.suffix_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:32.173807+00:00
-- url     : https://prove2.me/theorems/8c94fc80-d344-4a0e-b04e-b55f7590e212
-- title:
--   Fresh: suffix append right
-- statement:
--   The Fresh construction uses the suffix append right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L75-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L75-L76

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
omit [DecidableEq α]

theorem DeciSigma1.Holes.Fresh.suffix_append_right {a b : List α} (h : a <:+ b) (c : List α) : a ++ c <:+ b ++ c := by sorry
