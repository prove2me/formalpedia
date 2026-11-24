-- Prove2me | Theorems.Thm_FockSPR_blocks_disjoint
-- name    : FockSPR.blocks_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:14.91051+00:00
-- url     : https://prove2.me/theorems/97c7c7e5-f621-45ac-9955-6c84e94852e6
-- title:
--   Fock SPR: blocks disjoint
-- statement:
--   The Fock SPR construction uses the blocks disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L208-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L208-L225

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR

theorem FockSPR.blocks_disjoint {ℓ₁ ℓ₂ : ℕ} (h₁ : 1 ≤ ℓ₁) (h₂ : 1 ≤ ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    Disjoint (freqBlock ℓ₁) (freqBlock ℓ₂) := by sorry
