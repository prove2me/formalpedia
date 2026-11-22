-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_mem_throughOcc
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.mem_throughOcc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:58.560379+00:00
-- url     : https://prove2.me/theorems/346b2d5f-2f15-4f14-a1e5-920acb83c29e
-- title:
--   Block Deletion: mem through Occ
-- statement:
--   The Block Deletion construction uses the mem through Occ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L503-L505
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L503-L505

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.mem_throughOcc {l : Fin k} {o : Fin k × ℕ × ℕ} :
    o ∈ m.traversingOccurrences l ↔ o ∈ upperOccurrences W t ∧ o.1 = l ∧ m.edge.TraversedBy o := by sorry
