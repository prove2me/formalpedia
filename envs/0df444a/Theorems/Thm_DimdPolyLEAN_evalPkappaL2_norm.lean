-- Prove2me | Theorems.Thm_DimdPolyLEAN_evalPkappaL2_norm
-- name    : DimdPolyLEAN.evalPkappaL2_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:11.92354+00:00
-- url     : https://prove2.me/theorems/316efb1a-5878-40e9-96dd-04292e233e0d
-- title:
--   Dimd Poly LEAN: eval Pkappa L2 norm
-- statement:
--   The Dimd Poly LEAN construction uses the eval Pkappa L2 norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L142-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L142-L148

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

theorem DimdPolyLEAN.evalPkappaL2_norm
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    ‖evalPkappaL2 kappa F‖ = ‖F‖ := by sorry
