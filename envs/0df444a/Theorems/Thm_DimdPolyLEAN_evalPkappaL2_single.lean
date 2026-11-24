-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_single
-- name    : DimdPolyLEAN.evalPkappaL2_single
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:17:00.486795+00:00
-- url     : https://prove2.me/theorems/51cf7a6b-a2f7-4485-973d-452eb074161c
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 single
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L705-L713
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L705-L713

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

theorem DimdPolyLEAN.evalPkappaL2_single
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (alpha : Idx d) (c : ℂ) :
    evalPkappaL2 kappa (Finsupp.single alpha c : Pkappa d kappa) = c • PhiL2 kappa alpha := by sorry
