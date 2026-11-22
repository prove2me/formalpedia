-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_le_windowLength
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.le_windowLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:58.025795+00:00
-- url     : https://prove2.me/theorems/75f8c7d3-029f-4ec1-98bd-c408ba474fe0
-- title:
--   Block Deletion: le window Length
-- statement:
--   The Block Deletion construction uses the le window Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L164-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L164-L171

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.le_windowLength {r : ℕ} (hr1 : 1 ≤ r) (hrt : r ≤ t) {g : Fin k} (hg : g ∈ active W r)
    {u : List α} {c : ℕ} (hs : marker W r g <:+ u.take c) :
    (marker W r g).length ≤ windowLength W t u c := by sorry
