-- Prove2me | Theorems.Thm_DimdPolyLEAN_toFun_as_L2_eq_boxLimit
-- name    : DimdPolyLEAN.toFun_as_L2_eq_boxLimit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:21:20.606342+00:00
-- url     : https://prove2.me/theorems/7b9ba193-d4c0-4b9e-bf56-70acf17fcfa4
-- title:
--   Dimd Poly LEAN: to Fun as L2 eq box Limit
-- statement:
--   The Dimd Poly LEAN construction uses the to Fun as L2 eq box Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1291-L1296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L1291-L1296

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

theorem DimdPolyLEAN.toFun_as_L2_eq_boxLimit
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsTensorL2Rep (toL2 kappa U) (toFun kappa U) := by sorry
