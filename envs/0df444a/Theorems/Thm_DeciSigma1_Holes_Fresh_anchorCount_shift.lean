-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_shift
-- name    : DeciSigma1.Holes.Fresh.anchorCount_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:34.21081+00:00
-- url     : https://prove2.me/theorems/bccd79c7-f0ad-460d-9189-f7729598f332
-- title:
--   Fresh: anchor Count shift
-- statement:
--   The Fresh construction uses the anchor Count shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L339-L353
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L339-L353

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.anchorCount_shift {A Q : Finset ℕ} {base n lo : ℕ}
    (hag : ∀ q, lo ≤ q → q ≤ n → (base + q ∈ A ↔ q ∈ Q)) :
    anchorCount A (base + lo) (base + n) = anchorCount Q lo n := by sorry
