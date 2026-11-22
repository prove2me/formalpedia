-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_strictlySeparated
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.strictlySeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:05.642938+00:00
-- url     : https://prove2.me/theorems/75c55143-4dfe-4e7b-be93-a8abdc6de72f
-- title:
--   Block Deletion: strictly Separated
-- statement:
--   The Block Deletion construction uses the strictly Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L562-L564
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L562-L564

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.strictlySeparated (l : Fin k) :
    StrictlySeparated m.deletionLength (m.sites l) := by sorry
