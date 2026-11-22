-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_depthCut_anti
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.depthCut_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:17.991454+00:00
-- url     : https://prove2.me/theorems/37ef05ff-0469-4f11-9635-2b30f332a688
-- title:
--   Block Deletion: depth Cut anti
-- statement:
--   The Block Deletion construction uses the depth Cut anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L160-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L160-L165

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.depthCut_anti {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    {d d' : ℕ} (h : d ≤ d') (hd' : d' ≤ lowerBlockCount W t o) : depthCut W t o d' ≤
        depthCut W t o d := by sorry
