-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_card_depthCuts
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.card_depthCuts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:18.6186+00:00
-- url     : https://prove2.me/theorems/407df2db-7314-489a-9f0e-6935efe63fac
-- title:
--   Block Deletion: card depth Cuts
-- statement:
--   A set that contains the cuts at depths `0, …, D` of an upper occurrence has at least `D + 1`
--   elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L144-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L144-L158

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.card_depthCuts {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    {D : ℕ} (hD : D ≤ lowerBlockCount W t o) {X : Finset ℕ} (hX : ∀ d ≤ D, depthCut W t o d ∈ X) :
    D + 1 ≤ X.card := by sorry
