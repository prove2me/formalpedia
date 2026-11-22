-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_text
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.site_text
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:20.063006+00:00
-- url     : https://prove2.me/theorems/7486bd66-0661-4985-a9f8-420701752b0e
-- title:
--   Block Deletion: site text
-- statement:
--   The Block Deletion construction uses the site text property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L84-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L84-L99

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.site_text {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    c + m.deletionLength < (W l).length ∧ ((W l).drop c).take m.deletionLength = m.deletedText := by sorry
