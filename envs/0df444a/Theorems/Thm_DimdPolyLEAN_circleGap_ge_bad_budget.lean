-- Prove2me | Theorems.Thm_DimdPolyLEAN_circleGap_ge_bad_budget
-- name    : DimdPolyLEAN.circleGap_ge_bad_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:25.673968+00:00
-- url     : https://prove2.me/theorems/8b099bfb-f2ae-4e30-b6da-2c2364586fb8
-- title:
--   Dimd Poly LEAN: circle Gap ge bad budget
-- statement:
--   The Dimd Poly LEAN construction uses the circle Gap ge bad budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseCircleEstimate.lean#L733-L736
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseCircleEstimate.lean#L733-L736

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

theorem DimdPolyLEAN.circleGap_ge_bad_budget (D : Nat) :
    2 * circleBadConst D * circleGoodBudget D <= circleGap D := by sorry
