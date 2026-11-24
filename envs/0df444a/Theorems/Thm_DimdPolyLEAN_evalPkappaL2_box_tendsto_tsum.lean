-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_box_tendsto_tsum
-- name    : DimdPolyLEAN.evalPkappaL2_box_tendsto_tsum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:23.059816+00:00
-- url     : https://prove2.me/theorems/e2b215aa-b805-41d9-ac54-641959f57ca7
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 box tendsto tsum
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 box tendsto tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L770-L779
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L770-L779

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

theorem DimdPolyLEAN.evalPkappaL2_box_tendsto_tsum
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    Filter.Tendsto (fun J : MultiIndex d =>
        evalPkappaL2 kappa (truncateFinset (box J) U))
      Filter.atTop
      (nhds (∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha)) := by sorry
