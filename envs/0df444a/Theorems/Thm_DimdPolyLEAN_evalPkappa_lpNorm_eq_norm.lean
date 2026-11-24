-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappa_lpNorm_eq_norm
-- name    : DimdPolyLEAN.evalPkappa_lpNorm_eq_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:18.948807+00:00
-- url     : https://prove2.me/theorems/20a74f7d-8ffe-4d81-8262-7c45d117b310
-- title:
--   Dimd Poly LEAN: eval Pkappa lp Norm eq norm
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa lp Norm eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L126-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L126-L140

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
open DimdPolyLEAN

theorem DimdPolyLEAN.evalPkappa_lpNorm_eq_norm
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    lpNorm (evalPkappa kappa F) 2 (gammaD d) = ‖F‖ := by sorry
