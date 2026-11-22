-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_ne_right
-- name    : DeciSigma1.Holes.Fresh.StrictlySeparated.ne_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:58.699022+00:00
-- url     : https://prove2.me/theorems/ea2cc051-2c60-4e9f-9fcd-90e7ef54eb5c
-- title:
--   Strictly Separated: ne right
-- statement:
--   The Strictly Separated construction uses the ne right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L61-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L61-L65

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

theorem DeciSigma1.Holes.Fresh.StrictlySeparated.ne_right (h : StrictlySeparated δ cs) (hδ : 0 < δ) {c c' : ℕ}
    (hc : c ∈ cs) (hc' : c' ∈ cs) : c ≠ c' + δ := by sorry
