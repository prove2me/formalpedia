-- Prove2me | Theorems.Thm_DimdPolyLEAN_toFun_represents_toL2
-- name    : DimdPolyLEAN.toFun_represents_toL2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:34:57.733518+00:00
-- url     : https://prove2.me/theorems/96b244fa-491f-4673-af55-263caceb17a5
-- title:
--   Dimd Poly LEAN: to Fun represents to L2
-- statement:
--   The Dimd Poly LEAN construction uses the to Fun represents to L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1298-L1301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1298-L1301

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

theorem DimdPolyLEAN.toFun_represents_toL2
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsTensorL2Rep (toL2 kappa U) (toFun kappa U) := by sorry
