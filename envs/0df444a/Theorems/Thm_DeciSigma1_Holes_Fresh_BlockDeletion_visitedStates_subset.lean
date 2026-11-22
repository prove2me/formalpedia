-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_visitedStates_subset
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.visitedStates_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:57.542953+00:00
-- url     : https://prove2.me/theorems/bb4e134c-44a1-499e-8f2b-6ffcef27b8d6
-- title:
--   Block Deletion: visited States subset
-- statement:
--   The edited tuple visits only states that the original visits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L618-L624
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L618-L624

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.visitedStates_subset [DecidableEq S] (l : Fin k) :
    T.visitedStates m.apply l ⊆ T.visitedStates W l := by sorry
