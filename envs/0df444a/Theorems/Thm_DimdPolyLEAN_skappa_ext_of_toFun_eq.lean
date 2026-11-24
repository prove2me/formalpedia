-- Prove2me | Theorems.Thm_DimdPolyLEAN_skappa_ext_of_toFun_eq
-- name    : DimdPolyLEAN.skappa_ext_of_toFun_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:35:14.923589+00:00
-- url     : https://prove2.me/theorems/88e60bde-4f7a-4c14-8e11-61775437b2b5
-- title:
--   Dimd Poly LEAN: skappa ext of to Fun eq
-- statement:
--   The Dimd Poly LEAN construction uses the skappa ext of to Fun eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1374-L1383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1374-L1383

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

theorem DimdPolyLEAN.skappa_ext_of_toFun_eq
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d} {U V : Skappa d kappa}
    (h : ∀ z, toFun kappa U z = toFun kappa V z) :
    U = V := by sorry
