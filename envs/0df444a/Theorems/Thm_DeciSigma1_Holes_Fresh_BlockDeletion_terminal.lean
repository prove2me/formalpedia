-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_terminal
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:53.214059+00:00
-- url     : https://prove2.me/theorems/1403b6d6-f413-49b7-92a0-3dd68b10d768
-- title:
--   Block Deletion: terminal
-- statement:
--   No deletion site meets the last marker of level `t + 1` of its word, by the bound on anchors
--   inside a marker and the deletion margin.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L125-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L125-L156

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.terminal [DecidableEq S] (hfr : ∀ i, T.Fresh W i) {l : Fin k}
    (hl : l ∈ active W (t + 1)) {c : ℕ} (hc : c ∈ m.sites l) :
    c + m.deletionLength + (marker W (t + 1) l).length ≤ (W l).length := by sorry
