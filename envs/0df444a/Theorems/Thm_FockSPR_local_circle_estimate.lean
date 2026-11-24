-- Prove2me | Theorems.Thm_FockSPR_local_circle_estimate
-- name    : FockSPR.local_circle_estimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:49.392879+00:00
-- url     : https://prove2.me/theorems/48f28d9b-ec64-4cfd-9db2-5e8daa0064b9
-- title:
--   Fock SPR: local circle estimate
-- statement:
--   The Fock SPR construction uses the local circle estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LocalCircleEstimate.lean#L647-L670
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LocalCircleEstimate.lean#L647-L670

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCircleEstimate
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex Real Finset
noncomputable section
open FockSPR

theorem FockSPR.local_circle_estimate {L : ℕ} (hL : 1 ≤ L) {E : Finset ℕ}
    (hE : E.card = L) (hE_pos : ∀ n ∈ E, 1 ≤ n)
    (b : ℕ → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t => ∑ n ∈ E, b n * fourier (n : ℤ) t) :
    circleNormSq P ≤ 144 * L *
      (∫ t : AddCircle T, (rho (P t)) ^ 2
        ∂AddCircle.haarAddCircle) := by sorry
