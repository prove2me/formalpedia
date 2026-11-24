-- Prove2me | Theorems.Thm_FockSPR_fockNorm_decomposes
-- name    : FockSPR.fockNorm_decomposes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:26.060483+00:00
-- url     : https://prove2.me/theorems/e85b85a8-d63b-47fe-93c6-89725bbc6058
-- title:
--   Fock SPR: fock Norm decomposes
-- statement:
--   The Fock SPR construction uses the fock Norm decomposes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L247-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L247-L264

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR

theorem FockSPR.fockNorm_decomposes {D : ℕ} (a : Fin D → ℂ) :
    fockNormSq a = ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
      ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0 := by sorry
