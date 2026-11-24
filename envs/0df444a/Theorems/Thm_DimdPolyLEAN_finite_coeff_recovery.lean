-- Prove2me | Theorems.Thm_DimdPolyLEAN_finite_coeff_recovery
-- name    : DimdPolyLEAN.finite_coeff_recovery
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:08.832675+00:00
-- url     : https://prove2.me/theorems/53122f09-7d02-4e3e-9323-6a900b6e652d
-- title:
--   Dimd Poly LEAN: finite coeff recovery
-- statement:
--   The Dimd Poly LEAN construction uses the finite coeff recovery property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L715-L732
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L715-L732

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

theorem DimdPolyLEAN.finite_coeff_recovery
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa)
    (beta : Idx d) :
    coeffPkappa F beta = inner ℂ (PhiL2 kappa beta) (evalPkappaL2 kappa F) := by sorry
