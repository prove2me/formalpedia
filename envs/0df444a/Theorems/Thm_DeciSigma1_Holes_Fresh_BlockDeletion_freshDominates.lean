-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_freshDominates
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.freshDominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:22.077601+00:00
-- url     : https://prove2.me/theorems/80f3bd5b-18b6-436a-9e22-5f0c8c37550c
-- title:
--   Block Deletion: fresh Dominates
-- statement:
--   A block deletion on a fresh tuple is a fresh domination.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L596-L598
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L596-L598

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.freshDominates [DecidableEq S] (hfr : ∀ i, T.Fresh W i) :
    FreshDominates T m.apply W := by sorry
