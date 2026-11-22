-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_channel
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.channel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:15.388752+00:00
-- url     : https://prove2.me/theorems/9d746582-a967-4c06-a2a1-76a8b39d05de
-- title:
--   Block Deletion: channel
-- statement:
--   Every channel of the edited tuple, including those from a coordinate to itself and those
--   with empty target suffixes, is contained in the corresponding channel of the original tuple.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L572-L593
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L572-L593

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.channel [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    (i j : Fin k) : T.channel m.apply i j ⊆ T.channel W i j := by sorry
