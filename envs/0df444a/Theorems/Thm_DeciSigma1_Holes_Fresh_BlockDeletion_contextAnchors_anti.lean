-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_contextAnchors_anti
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.contextAnchors_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:26.206796+00:00
-- url     : https://prove2.me/theorems/a3c95286-b7eb-4a00-9ea7-a7fed992fa8f
-- title:
--   Block Deletion: context Anchors anti
-- statement:
--   The Block Deletion construction uses the context Anchors anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L158-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L158-L162

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

theorem DeciSigma1.Holes.Fresh.BlockDeletion.contextAnchors_anti {s t' : ℕ} (h : s ≤ t') (u : List α) :
    contextAnchors W t' u ⊆ contextAnchors W s u := by sorry
