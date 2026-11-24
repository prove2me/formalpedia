-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_zero
-- name    : DimdPolyLEAN.evalPkappaL2_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:27.097281+00:00
-- url     : https://prove2.me/theorems/c5b76264-1ff9-443a-bd06-46c5c60e11d8
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 zero
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L677-L680
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L677-L680

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

theorem DimdPolyLEAN.evalPkappaL2_zero
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    evalPkappaL2 kappa (0 : Pkappa d kappa) = 0 := by sorry
