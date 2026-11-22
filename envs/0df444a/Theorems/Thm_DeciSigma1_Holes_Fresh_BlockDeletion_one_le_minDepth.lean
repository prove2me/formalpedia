-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_one_le_minDepth
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.one_le_minDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:52.452095+00:00
-- url     : https://prove2.me/theorems/1f82b2e6-b387-4921-8a43-01aaea32a46d
-- title:
--   Block Deletion: one le min Depth
-- statement:
--   The Block Deletion construction uses the one le min Depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L496-L497
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L496-L497

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.one_le_minDepth :
    1 ≤ m.minDepth := by sorry
