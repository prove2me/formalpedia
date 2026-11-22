-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_apply_of_inactive
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.apply_of_inactive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:52.51916+00:00
-- url     : https://prove2.me/theorems/6a63ea0a-b344-4b97-8001-656777c9cc76
-- title:
--   Block Deletion: apply of inactive
-- statement:
--   A word that is not active at level `t + 1` has no deletion site and is not edited.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L112-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L112-L121

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.apply_of_inactive {l : Fin k} (hl : l ∉ active W (t + 1)) :
    m.sites l = ∅ ∧ m.apply l = W l := by sorry
