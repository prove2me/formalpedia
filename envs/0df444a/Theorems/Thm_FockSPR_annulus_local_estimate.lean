-- Prove2me | Theorems.Thm_FockSPR_annulus_local_estimate
-- name    : FockSPR.annulus_local_estimate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:49.341598+00:00
-- url     : https://prove2.me/theorems/4d837c68-cfd6-4c34-b780-0b8a74887d4f
-- title:
--   Fock SPR: annulus local estimate
-- statement:
--   The Fock SPR construction uses the annulus local estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/AnnulusLocalEstimate.lean#L408-L418
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/AnnulusLocalEstimate.lean#L408-L418

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCircleEstimate
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_AnnulusLocalEstimate
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex Real Finset
noncomputable section
open FockSPR

theorem FockSPR.annulus_local_estimate {D : ℕ} (hD : 1 ≤ D) (a : Fin D → ℂ)
    (j : ℕ) {r : ℝ} (hr_nn : 0 ≤ r) (_hr_lo : (j : ℝ) ≤ r)
    (_hr_hi : r ≤ (j : ℝ) + 1) :
    circleNormSq (fun t => localPoly a 5 j (↑r * (fourier 1 t : ℂ))) ≤
      1620 ^ 2 *
        (∫ t : AddCircle T,
          (rho (localPoly a 5 j (↑r * (fourier 1 t : ℂ)))) ^ 2
          ∂AddCircle.haarAddCircle) := by sorry
