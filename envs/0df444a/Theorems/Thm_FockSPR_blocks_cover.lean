-- Prove2me | Theorems.Thm_FockSPR_blocks_cover
-- name    : FockSPR.blocks_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:24.484383+00:00
-- url     : https://prove2.me/theorems/c3d26a7a-529b-446f-94db-b24971d7e4e5
-- title:
--   Fock SPR: blocks cover
-- statement:
--   The Fock SPR construction uses the blocks cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L231-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L231-L239

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR

theorem FockSPR.blocks_cover (D : ℕ) (n : ℕ) (hn : 1 ≤ n) (_hnD : n ≤ D) :
    ∃ ℓ, 1 ≤ ℓ ∧ n ∈ freqBlock ℓ := by sorry
