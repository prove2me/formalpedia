-- Prove2me | Theorems.Thm_DimdPolyLEAN_pkappaInner_smul_left
-- name    : DimdPolyLEAN.pkappaInner_smul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:12.351787+00:00
-- url     : https://prove2.me/theorems/322d3103-3e1f-4e38-9537-467a61acf17b
-- title:
--   Dimd Poly LEAN: pkappa Inner smul left
-- statement:
--   The Dimd Poly LEAN construction uses the pkappa Inner smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L59-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L59-L70

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

theorem DimdPolyLEAN.pkappaInner_smul_left
    {d : Nat} {kappa : MultiIndex d} (c : ℂ)
    (Q F : Pkappa d kappa) :
    pkappaInner (c • Q) F = c * pkappaInner Q F := by sorry
