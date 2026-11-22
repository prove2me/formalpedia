-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_compatible_window
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.compatible_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:08.525813+00:00
-- url     : https://prove2.me/theorems/b1881e1a-1a83-42af-a809-c2565618fd7b
-- title:
--   Block Deletion: compatible window
-- statement:
--   The label window of a deletion site meets no other site of its word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L253-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L253-L296

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.compatible_window [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {l : Fin k} {c c₂ : ℕ} (hc : c ∈ m.sites l) (hc₂ : c₂ ∈ m.sites l) (hlt : c₂ < c) :
    c₂ + m.deletionLength + windowLength W t (W l) c ≤ c := by sorry
