-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_minDepth_le_endDepth
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.minDepth_le_endDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:33.030402+00:00
-- url     : https://prove2.me/theorems/c2e88435-9eca-452b-962e-bacf149e9d9b
-- title:
--   Block Deletion: min Depth le end Depth
-- statement:
--   The Block Deletion construction uses the min Depth le end Depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L65-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L65-L68

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.minDepth_le_endDepth :
    m.minDepth ≤
        m.edge.endDepth := by sorry
