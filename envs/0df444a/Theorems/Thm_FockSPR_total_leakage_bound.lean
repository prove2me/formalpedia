-- Prove2me | Theorems.Thm_FockSPR_total_leakage_bound
-- name    : FockSPR.total_leakage_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:56.567078+00:00
-- url     : https://prove2.me/theorems/db4b0037-2c5a-41ac-96f7-d8adb91968fd
-- title:
--   Fock SPR: total leakage bound
-- statement:
--   The Fock SPR construction uses the total leakage bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LeakageEstimate.lean#L826-L946
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LeakageEstimate.lean#L826-L946

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

theorem FockSPR.total_leakage_bound {D : ℕ} (a : Fin D → ℂ) {M : ℕ} (hM : 2 ≤ M) :
    ∀ ε > 0, ∃ bound, ∀ J ≥ bound,
    (∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖remainderPoly a M j (↑r * (fourier 1 t : ℂ))‖ ^ 2
          ∂AddCircle.haarAddCircle)) ≤
    (etaCoeff M J + ε) * fockNormSq a := by sorry
