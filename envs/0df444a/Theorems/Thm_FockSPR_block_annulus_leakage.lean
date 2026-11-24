-- Prove2me | Theorems.Thm_FockSPR_block_annulus_leakage
-- name    : FockSPR.block_annulus_leakage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:22.333206+00:00
-- url     : https://prove2.me/theorems/c21e9562-4211-42c4-a6be-559aefcf02a6
-- title:
--   Fock SPR: block annulus leakage
-- statement:
--   The Fock SPR construction uses the block annulus leakage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LeakageEstimate.lean#L272-L381
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LeakageEstimate.lean#L272-L381

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LeakageEstimate
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Real Finset Complex
noncomputable section
open FockSPR

theorem FockSPR.block_annulus_leakage {D : ℕ} (a : Fin D → ℂ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (j : ℕ) :
    2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖blockPoly a ℓ (↑r * (fourier 1 t : ℂ))‖ ^ 2
        ∂AddCircle.haarAddCircle) ≤
      Real.exp (1 / 4) *
        Real.exp (-(max ((j : ℤ) - ℓ - 1) 0 : ℤ) ^ 2) *
        (∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
          then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0) := by sorry
