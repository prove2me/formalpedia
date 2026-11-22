-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_lt
-- name    : DeciSigma1.Holes.Fresh.StrictlySeparated.lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:20.669628+00:00
-- url     : https://prove2.me/theorems/639ed4ba-5731-4e84-b237-f188be2e8366
-- title:
--   Strictly Separated: lt
-- statement:
--   The Strictly Separated construction uses the lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L58-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L58-L59

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

theorem DeciSigma1.Holes.Fresh.StrictlySeparated.lt (h : StrictlySeparated δ cs) {c c' : ℕ} (hc : c ∈ cs)
    (hc' : c' ∈ cs) (hlt : c < c') : c + δ < c' := by sorry
