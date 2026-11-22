-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_properVisitedStates_subset
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.properVisitedStates_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:03.280805+00:00
-- url     : https://prove2.me/theorems/db89e58f-904e-476e-a523-f63b8110bb4f
-- title:
--   Block Deletion: proper Visited States subset
-- statement:
--   The Block Deletion construction uses the proper Visited States subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L626-L631
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L626-L631

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.properVisitedStates_subset [DecidableEq S] (l : Fin k) :
    T.properVisitedStates m.apply l ⊆ T.properVisitedStates W l := by sorry
