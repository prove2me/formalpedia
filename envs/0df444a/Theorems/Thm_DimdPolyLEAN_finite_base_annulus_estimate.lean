-- Prove2me | Theorems.Thm_DimdPolyLEAN_finite_base_annulus_estimate
-- name    : DimdPolyLEAN.finite_base_annulus_estimate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:19:54.200851+00:00
-- url     : https://prove2.me/theorems/061a93d5-8c19-474c-819f-4a6a7611d7f4
-- title:
--   Dimd Poly LEAN: finite base annulus estimate
-- statement:
--   The Dimd Poly LEAN construction uses the finite base annulus estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseAnnulusEstimate.lean#L2221-L2273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseAnnulusEstimate.lean#L2221-L2273

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseCircleEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductAnnulusCircle
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open DimdPolyLEAN

theorem DimdPolyLEAN.finite_base_annulus_estimate
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF : basePointNormalized F) :
    ∀ eps : ℝ, 0 < eps ->
      ∃ J : Nat, ∃ C : ℝ, 0 < C ∧
        ∀ {H : Pkappa d kappa} {t eta : ℝ},
          ‖H‖ = 1 ->
          0 < t ->
          t <= 4 ->
          0 <= eta ->
          defect F (t • H) <= eta * t ->
          highAnnulusMass J (ofPkappa kappa H) <= C * eta ^ 2 + eps := by sorry
