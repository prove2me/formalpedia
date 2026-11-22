-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_windowLength_spec
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.windowLength_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:20.979306+00:00
-- url     : https://prove2.me/theorems/f40022a0-c128-4a34-9dd0-502c09e893b6
-- title:
--   Block Deletion: window Length spec
-- statement:
--   The Block Deletion construction uses the window Length spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L173-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L173-L189

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.windowLength_spec {u : List α} {c : ℕ} (hw : 0 < windowLength W t u c) :
    ∃ r, 1 ≤ r ∧ r ≤ t ∧ ∃ g ∈ active W r, marker W r g <:+ u.take c ∧
      (marker W r g).length = windowLength W t u c := by sorry
