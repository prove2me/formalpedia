-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_take_of_suffix_take
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.take_of_suffix_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:58.769047+00:00
-- url     : https://prove2.me/theorems/db459895-c4a9-4db4-911e-fc7b7151a6f5
-- title:
--   Block Deletion: take of suffix take
-- statement:
--   A text ending at a cut, read back from the cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L193-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelPreservation.lean#L193-L215

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
omit [DecidableEq α] [Fintype S]

theorem DeciSigma1.Holes.Fresh.BlockDeletion.take_of_suffix_take {x τ : List α} {c : ℕ} (hc : c ≤ x.length) (hs : τ <:+ x.take c)
    {e : ℕ} (he : e ≤ τ.length) :
    x.take (c - e) = x.take (c - τ.length) ++ τ.take (τ.length - e) ∧
      (x.drop (c - e)).take e = τ.drop (τ.length - e) := by sorry
