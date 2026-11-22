-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_mem_sites
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.mem_sites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:07.836955+00:00
-- url     : https://prove2.me/theorems/7ecc00df-b0a1-44f1-8e3a-ff3e382254e8
-- title:
--   Block Deletion: mem sites
-- statement:
--   The Block Deletion construction uses the mem sites property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L537-L544
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L537-L544

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.mem_sites {l : Fin k} {c : ℕ} :
    c ∈ m.sites l ↔ ∃ o ∈ upperOccurrences W t, o.1 = l ∧ m.edge.TraversedBy o ∧
        depthCut W t o m.maxDepth =
        c := by sorry
