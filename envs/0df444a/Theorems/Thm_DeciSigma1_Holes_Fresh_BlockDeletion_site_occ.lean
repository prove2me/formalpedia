-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_occ
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.site_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:11.017728+00:00
-- url     : https://prove2.me/theorems/14a67e1b-7f0a-41c0-8d8e-1dd500950c53
-- title:
--   Block Deletion: site occ
-- statement:
--   The Block Deletion construction uses the site occ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L80-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L80-L82

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.site_occ {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    ∃ o ∈ upperOccurrences W t, o.1 = l ∧ m.edge.TraversedBy o ∧ depthCut W t o m.maxDepth = c := by sorry
