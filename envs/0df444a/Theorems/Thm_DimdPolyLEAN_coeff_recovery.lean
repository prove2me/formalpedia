-- Prove2me | Theorems.Thm_DimdPolyLEAN_coeff_recovery
-- name    : DimdPolyLEAN.coeff_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:18:21.783922+00:00
-- url     : https://prove2.me/theorems/cd3c84ef-849b-4915-8360-7fc9df19db2a
-- title:
--   Dimd Poly LEAN: coeff recovery
-- statement:
--   The Dimd Poly LEAN construction uses the coeff recovery property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1303-L1337
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1303-L1337

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

theorem DimdPolyLEAN.coeff_recovery
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (beta : Idx d) :
    coeffSkappa U beta = inner ℂ (PhiL2 kappa beta) (toL2 kappa U) := by sorry
