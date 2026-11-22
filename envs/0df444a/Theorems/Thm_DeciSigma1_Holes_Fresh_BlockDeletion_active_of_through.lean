-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_active_of_through
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.active_of_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:17.7281+00:00
-- url     : https://prove2.me/theorems/82e5140d-9b44-4362-b9c5-faebf639a195
-- title:
--   Block Deletion: active of through
-- statement:
--   A word with an upper occurrence that traverses the edge is active at level `t + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L115-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L115-L136

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.active_of_through {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) : o.1 ∈ active W (t + 1) := by sorry
