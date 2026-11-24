-- Prove2me | Theorems.Thm_DimdPolyLEAN_finite_base_product_annulus_estimate
-- name    : DimdPolyLEAN.finite_base_product_annulus_estimate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:25:30.559639+00:00
-- url     : https://prove2.me/theorems/ee93a576-4d12-4e9e-9ec7-5a64c79ea0d4
-- title:
--   Dimd Poly LEAN: finite base product annulus estimate
-- statement:
--   The Dimd Poly LEAN construction uses the finite base product annulus estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseAnnulusEstimate.lean#L2075-L2219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseAnnulusEstimate.lean#L2075-L2219

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

theorem DimdPolyLEAN.finite_base_product_annulus_estimate
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF : basePointNormalized F) :
    ∀ eps : ℝ, 0 < eps ->
      ∃ J : Nat, ∃ M : Nat, 1 <= M ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ G : Pkappa d kappa,
          highAnnulusMass J (ofPkappa kappa G)
            <= C * defect F G ^ 2 + eps * ‖G‖ ^ 2 := by sorry
