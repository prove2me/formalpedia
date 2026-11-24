-- Prove2me | Theorems.Thm_DimdPolyLEAN_summable_skappa_eval_mul
-- name    : DimdPolyLEAN.summable_skappa_eval_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:22.002426+00:00
-- url     : https://prove2.me/theorems/ae0d891c-defe-43b5-89e2-bd12a45d87fc
-- title:
--   Dimd Poly LEAN: summable skappa eval mul
-- statement:
--   The Dimd Poly LEAN construction uses the summable skappa eval mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L444-L447
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean#L444-L447

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

theorem DimdPolyLEAN.summable_skappa_eval_mul
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha z) := by sorry
