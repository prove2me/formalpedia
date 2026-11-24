-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappa_zero
-- name    : DimdPolyLEAN.evalPkappa_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:02.753008+00:00
-- url     : https://prove2.me/theorems/a65699fd-13c5-4e8d-9517-af4a37023d3c
-- title:
--   Dimd Poly LEAN: eval Pkappa zero
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L39-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L39-L44

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

theorem DimdPolyLEAN.evalPkappa_zero
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    evalPkappa kappa (0 : Pkappa d kappa) = 0 := by sorry
