-- Prove2me | Theorems.Thm_FockSPR_blocks_orthogonal_circle
-- name    : FockSPR.blocks_orthogonal_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:29.881925+00:00
-- url     : https://prove2.me/theorems/d32ffa54-6e61-4e15-a79d-ea1b51955399
-- title:
--   Fock SPR: blocks orthogonal circle
-- statement:
--   The Fock SPR construction uses the blocks orthogonal circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L273-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L273-L292

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR

theorem FockSPR.blocks_orthogonal_circle {D : ℕ} (a : Fin D → ℂ) {ℓ₁ ℓ₂ : ℕ}
    (_h₁ : 1 ≤ ℓ₁) (_h₂ : 1 ≤ ℓ₂) (hne : ℓ₁ ≠ ℓ₂) (r : ℝ) (_hr : 0 ≤ r) :
    ∫ t : AddCircle T,
      (blockPoly a ℓ₁ (↑r * (fourier 1 t : ℂ))) *
      starRingEnd ℂ (blockPoly a ℓ₂ (↑r * (fourier 1 t : ℂ)))
      ∂AddCircle.haarAddCircle = 0 := by sorry
