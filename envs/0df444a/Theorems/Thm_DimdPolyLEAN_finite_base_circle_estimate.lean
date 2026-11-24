-- Prove2me | Theorems.Thm_DimdPolyLEAN_finite_base_circle_estimate
-- name    : DimdPolyLEAN.finite_base_circle_estimate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:29.509076+00:00
-- url     : https://prove2.me/theorems/41c4ce14-7004-4241-ae6b-a2eabbd96ed3
-- title:
--   Dimd Poly LEAN: finite base circle estimate
-- statement:
--   The Dimd Poly LEAN construction uses the finite base circle estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseCircleEstimate.lean#L4705-L4872
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseCircleEstimate.lean#L4705-L4872

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_SafeSquare
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MissingMathlib_Poincare
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Order.Interval.Set.Union
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseCircleEstimate
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN

theorem DimdPolyLEAN.finite_base_circle_estimate
    (D : Nat) :
    ∀ {L N : Nat}, 1 <= L ->
      circleGap D * L <= N ->
      ∀ (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ),
        circleL2Sq (bandPoly N p) <=
          circleConst D * defectSq (lowPoly q) (bandPoly N p) := by sorry
