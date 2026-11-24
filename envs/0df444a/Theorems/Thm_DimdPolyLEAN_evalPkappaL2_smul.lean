-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_smul
-- name    : DimdPolyLEAN.evalPkappaL2_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:09.947752+00:00
-- url     : https://prove2.me/theorems/8d65a688-3e0f-495b-8a4c-ff7e31cdc84a
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 smul
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L661-L675
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L661-L675

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

theorem DimdPolyLEAN.evalPkappaL2_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (c : ℂ) (F : Pkappa d kappa) :
    evalPkappaL2 kappa (c • F) = c • evalPkappaL2 kappa F := by sorry
