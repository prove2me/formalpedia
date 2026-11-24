-- Prove2me | Theorems.Thm_DimdPolyLEAN_orthogonal_coercivity
-- name    : DimdPolyLEAN.orthogonal_coercivity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:01.054808+00:00
-- url     : https://prove2.me/theorems/e4b91f01-d985-439e-b609-136823b0001a
-- title:
--   Dimd Poly LEAN: orthogonal coercivity
-- statement:
--   The Dimd Poly LEAN construction uses the orthogonal coercivity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/OrthogonalCoercivity.lean#L155-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/OrthogonalCoercivity.lean#L155-L250

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
variable {d : Nat} (kappa : MultiIndex d)
local notation "Pk" => Pkappa d kappa

theorem DimdPolyLEAN.orthogonal_coercivity
    (hd : 0 < d) (F : Pk) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1) :
    ∃ C_F_perp : ℝ, 0 < C_F_perp ∧
      ∀ G : Pk, OrthogonalToPk kappa F G ->
        ‖G‖ <= C_F_perp * defectPk kappa F G := by sorry
