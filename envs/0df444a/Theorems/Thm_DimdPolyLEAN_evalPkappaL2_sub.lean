-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_sub
-- name    : DimdPolyLEAN.evalPkappaL2_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:25:59.89327+00:00
-- url     : https://prove2.me/theorems/d9cb122d-618e-459b-b405-2a6e3fe6a14e
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 sub
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L150-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L150-L158

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

theorem DimdPolyLEAN.evalPkappaL2_sub
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappaL2 kappa (F - G) = evalPkappaL2 kappa F - evalPkappaL2 kappa G := by sorry
