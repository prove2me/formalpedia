-- Prove2me | Theorems.Thm_FockSPR_freqBlock_card
-- name    : FockSPR.freqBlock_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:55.49471+00:00
-- url     : https://prove2.me/theorems/b6442efd-9343-40cc-86a0-9513aa179bd2
-- title:
--   Fock SPR: freq Block card
-- statement:
--   The cardinality of `freqBlock ℓ` is `2ℓ + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L105-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L105-L108

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR

theorem FockSPR.freqBlock_card (ℓ : ℕ) : (freqBlock ℓ).card = 2 * ℓ + 1 := by sorry
