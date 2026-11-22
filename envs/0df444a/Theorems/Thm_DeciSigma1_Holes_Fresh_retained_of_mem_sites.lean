-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_retained_of_mem_sites
-- name    : DeciSigma1.Holes.Fresh.retained_of_mem_sites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:13.133428+00:00
-- url     : https://prove2.me/theorems/cb4b6cc6-aff3-467d-b670-0cba237f8466
-- title:
--   Fresh: retained of mem sites
-- statement:
--   The Fresh construction uses the retained of mem sites property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L67-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L67-L71

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

theorem DeciSigma1.Holes.Fresh.retained_of_mem_sites (hs : StrictlySeparated δ cs) {c : ℕ} (hc : c ∈ cs) :
    Retained δ cs c := by sorry
