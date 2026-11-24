-- Prove2me | Theorems.Thm_DimdPolyLEAN_coeff_ofPkappa
-- name    : DimdPolyLEAN.coeff_ofPkappa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:17:58.250374+00:00
-- url     : https://prove2.me/theorems/fc2ca4c3-d1c9-4ba6-8621-967e2951a73f
-- title:
--   Dimd Poly LEAN: coeff of Pkappa
-- statement:
--   The Dimd Poly LEAN construction uses the coeff of Pkappa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L33-L37
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L33-L37

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

theorem DimdPolyLEAN.coeff_ofPkappa
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) (alpha : Idx d) :
    coeffSkappa (ofPkappa kappa F) alpha = coeffPkappa F alpha := by sorry
