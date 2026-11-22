-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_retained_length
-- name    : DeciSigma1.Holes.Fresh.retained_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:12.703649+00:00
-- url     : https://prove2.me/theorems/113bf0e0-7830-4879-83bc-674064f15329
-- title:
--   Fresh: retained length
-- statement:
--   The Fresh construction uses the retained length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L73-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L73-L74

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.retained_length {n : ℕ} (h : ∀ c ∈ cs, c + δ ≤ n) : Retained δ cs n := by sorry
