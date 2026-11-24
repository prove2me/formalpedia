-- Prove2me | Theorems.Thm_DimdPolyLEAN_toFun_smul_complex
-- name    : DimdPolyLEAN.toFun_smul_complex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:35:13.906981+00:00
-- url     : https://prove2.me/theorems/3699ce53-dc53-41cf-93eb-8e86fb4f8933
-- title:
--   Dimd Poly LEAN: to Fun smul complex
-- statement:
--   The Dimd Poly LEAN construction uses the to Fun smul complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1364-L1372
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1364-L1372

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

theorem DimdPolyLEAN.toFun_smul_complex
    {d : Nat} (kappa : MultiIndex d) (w : ℂ) (U : Skappa d kappa) :
    toFun kappa (w • U) = fun z => w * toFun kappa U z := by sorry
