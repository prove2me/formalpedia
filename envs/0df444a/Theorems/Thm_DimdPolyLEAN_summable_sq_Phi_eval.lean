-- Prove2me | Theorems.Thm_DimdPolyLEAN_summable_sq_Phi_eval
-- name    : DimdPolyLEAN.summable_sq_Phi_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:51.315013+00:00
-- url     : https://prove2.me/theorems/6cf77e1c-1dc5-4376-b8b1-67e847f56654
-- title:
--   Dimd Poly LEAN: summable sq Phi eval
-- statement:
--   The Dimd Poly LEAN construction uses the summable sq Phi eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L376-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L376-L421

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

theorem DimdPolyLEAN.summable_sq_Phi_eval
    {d : Nat} (kappa : MultiIndex d) (z : Cd d) :
    Summable (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) := by sorry
