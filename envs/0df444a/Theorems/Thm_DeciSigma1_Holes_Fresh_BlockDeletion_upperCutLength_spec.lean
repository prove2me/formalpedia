-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_upperCutLength_spec
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.upperCutLength_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:21.935674+00:00
-- url     : https://prove2.me/theorems/537a1829-47c0-4f89-9a03-2ce465b92b3a
-- title:
--   Block Deletion: upper Cut Length spec
-- statement:
--   The Block Deletion construction uses the upper Cut Length spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L70-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ChannelTransport.lean#L70-L78

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.upperCutLength_spec {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) :
    depthCut W t o m.minDepth + m.upperCutLength = o.2.2 ∧ depthCut W t o m.maxDepth +
        m.deletionLength +
        m.upperCutLength = o.2.2 ∧
      0 < m.upperCutLength := by sorry
