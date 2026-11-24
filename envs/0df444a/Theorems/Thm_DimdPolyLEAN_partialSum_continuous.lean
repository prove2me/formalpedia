-- Prove2me | Theorems.Thm_DimdPolyLEAN_partialSum_continuous
-- name    : DimdPolyLEAN.partialSum_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:02.679999+00:00
-- url     : https://prove2.me/theorems/be0fa68a-1bdd-4f71-adb5-3c1639cca373
-- title:
--   Dimd Poly LEAN: partial Sum continuous
-- statement:
--   The Dimd Poly LEAN construction uses the partial Sum continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1231-L1239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1231-L1239

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

theorem DimdPolyLEAN.partialSum_continuous
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (J : MultiIndex d) :
    Continuous (partialSum kappa U J) := by sorry
