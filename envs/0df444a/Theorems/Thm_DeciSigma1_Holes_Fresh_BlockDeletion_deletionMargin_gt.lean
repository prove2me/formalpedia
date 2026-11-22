-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_deletionMargin_gt
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.deletionMargin_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:42.179673+00:00
-- url     : https://prove2.me/theorems/807e7daa-ad95-4be4-a9df-10ef1ae8c50b
-- title:
--   Block Deletion: deletion Margin gt
-- statement:
--   The Block Deletion construction uses the deletion Margin gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L167-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L167-L170

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

theorem DeciSigma1.Holes.Fresh.BlockDeletion.deletionMargin_gt
    (hlt : m.edge.startDepth + deletionMargin k (Fintype.card S) ≤ m.minDepth) :
    k * (Fintype.card S - 1) + 4 + m.edge.startDepth < m.minDepth := by sorry
