-- Prove2me | Theorems.Thm_DimdPolyLEAN_partialSum_tendsto_toFun_pointwise
-- name    : DimdPolyLEAN.partialSum_tendsto_toFun_pointwise
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:19.948236+00:00
-- url     : https://prove2.me/theorems/87a1f9fe-41e7-4ad1-a9e7-05b63f460894
-- title:
--   Dimd Poly LEAN: partial Sum tendsto to Fun pointwise
-- statement:
--   The Dimd Poly LEAN construction uses the partial Sum tendsto to Fun pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L534-L539
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L534-L539

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

theorem DimdPolyLEAN.partialSum_tendsto_toFun_pointwise
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d) :
    Filter.Tendsto (fun J : MultiIndex d => partialSum kappa U J z)
      Filter.atTop (nhds (toFun kappa U z)) := by sorry
