-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappa_smul
-- name    : DimdPolyLEAN.evalPkappa_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:03.781107+00:00
-- url     : https://prove2.me/theorems/62274b20-a6f9-44f3-9f47-bd413534b593
-- title:
--   Dimd Poly LEAN: eval Pkappa smul
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L54-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L54-L68

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

theorem DimdPolyLEAN.evalPkappa_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (c : ℂ) (F : Pkappa d kappa) :
    evalPkappa kappa (c • F) = fun z => c * evalPkappa kappa F z := by sorry
