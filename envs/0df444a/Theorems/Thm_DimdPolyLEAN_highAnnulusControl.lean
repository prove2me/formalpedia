-- Prove2me | Theorems.Thm_DimdPolyLEAN_highAnnulusControl
-- name    : DimdPolyLEAN.highAnnulusControl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:25:34.749336+00:00
-- url     : https://prove2.me/theorems/d63474db-23e7-4a82-b171-72c2344e57f7
-- title:
--   Dimd Poly LEAN: high Annulus Control
-- statement:
--   The Dimd Poly LEAN construction uses the high Annulus Control property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseAnnulusEstimate.lean#L2275-L2319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseAnnulusEstimate.lean#L2275-L2319

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

theorem DimdPolyLEAN.highAnnulusControl
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1) :
    ∃ J : Nat, ∃ delta_high : ℝ, 0 < delta_high ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        defect F (t • H) <= delta_high * t ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by sorry
