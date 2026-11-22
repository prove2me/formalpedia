-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_length_not_mem_sitePositions
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.length_not_mem_sitePositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:33.325177+00:00
-- url     : https://prove2.me/theorems/63b29462-74dc-41e7-83be-c0f89f35be45
-- title:
--   Block Deletion: length not mem site Positions
-- statement:
--   The Block Deletion construction uses the length not mem site Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L596-L601
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L596-L601

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
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

theorem DeciSigma1.Holes.Fresh.BlockDeletion.length_not_mem_sitePositions (l : Fin k) :
    (W l).length ∉ sitePositions m.deletionLength (m.sites l) := by sorry
