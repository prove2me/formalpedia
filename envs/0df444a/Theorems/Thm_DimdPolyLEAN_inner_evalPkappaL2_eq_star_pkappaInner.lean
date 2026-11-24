-- Prove2me | Theorems.Thm_DimdPolyLEAN_inner_evalPkappaL2_eq_star_pkappaInner
-- name    : DimdPolyLEAN.inner_evalPkappaL2_eq_star_pkappaInner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:11.456978+00:00
-- url     : https://prove2.me/theorems/0bc91947-c87a-4181-bde3-bd1c58c5572f
-- title:
--   Dimd Poly LEAN: inner eval Pkappa L2 eq star pkappa Inner
-- statement:
--   The Dimd Poly LEAN construction uses the inner eval Pkappa L2 eq star pkappa Inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L160-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean#L160-L180

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

theorem DimdPolyLEAN.inner_evalPkappaL2_eq_star_pkappaInner
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (G F : Pkappa d kappa) :
    inner ℂ (evalPkappaL2 kappa G) (evalPkappaL2 kappa F) = star (pkappaInner G F) := by sorry
