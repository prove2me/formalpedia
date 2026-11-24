-- Prove2me | Theorems.Thm_DimdPolyLEAN_lowAnnulusDefectControl
-- name    : DimdPolyLEAN.lowAnnulusDefectControl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:45.328729+00:00
-- url     : https://prove2.me/theorems/10eb04ba-7196-46a8-b568-65a5fef25342
-- title:
--   Dimd Poly LEAN: low Annulus Defect Control
-- statement:
--   The Dimd Poly LEAN construction uses the low Annulus Defect Control property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/CoefficientLimitRigidity.lean#L2772-L2802
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/CoefficientLimitRigidity.lean#L2772-L2802

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN

theorem DimdPolyLEAN.lowAnnulusDefectControl
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    (J : Nat) :
    ∃ delta_low : ℝ, 0 < delta_low ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        defect F (t • H) <= delta_low * t ->
        lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by sorry
