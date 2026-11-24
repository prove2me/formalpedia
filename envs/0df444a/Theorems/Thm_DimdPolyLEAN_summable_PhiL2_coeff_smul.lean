-- Prove2me | Theorems.Thm_DimdPolyLEAN_summable_PhiL2_coeff_smul
-- name    : DimdPolyLEAN.summable_PhiL2_coeff_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:51.640595+00:00
-- url     : https://prove2.me/theorems/8842f341-0d76-4434-b0ee-5ba4de66bb78
-- title:
--   Dimd Poly LEAN: summable Phi L2 coeff smul
-- statement:
--   The Dimd Poly LEAN construction uses the summable Phi L2 coeff smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L742-L752
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L742-L752

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

theorem DimdPolyLEAN.summable_PhiL2_coeff_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha • PhiL2 kappa alpha) := by sorry
