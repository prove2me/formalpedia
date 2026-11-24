-- Prove2me | Theorems.Thm_DimdPolyLEAN_continuous_limit_of_locallyUniform_boxPartialSums
-- name    : DimdPolyLEAN.continuous_limit_of_locallyUniform_boxPartialSums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:20.612769+00:00
-- url     : https://prove2.me/theorems/247a3f7b-b73c-4899-86d3-54f1f6d46338
-- title:
--   Dimd Poly LEAN: continuous limit of locally Uniform box Partial Sums
-- statement:
--   The Dimd Poly LEAN construction uses the continuous limit of locally Uniform box Partial Sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1282-L1289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1282-L1289

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN

theorem DimdPolyLEAN.continuous_limit_of_locallyUniform_boxPartialSums
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    {f : Cd d -> ℂ}
    (hlim : BoxPartialSumsLocallyUniformTo kappa U f) :
    Continuous f := by sorry
