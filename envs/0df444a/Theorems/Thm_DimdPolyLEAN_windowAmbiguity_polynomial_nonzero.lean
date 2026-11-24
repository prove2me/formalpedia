-- Prove2me | Theorems.Thm_DimdPolyLEAN_windowAmbiguity_polynomial_nonzero
-- name    : DimdPolyLEAN.windowAmbiguity_polynomial_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:40:58.280887+00:00
-- url     : https://prove2.me/theorems/f980d4ce-ccbb-4304-972c-595f0511cd56
-- title:
--   Dimd Poly LEAN: window Ambiguity polynomial nonzero
-- statement:
--   The Dimd Poly LEAN construction uses the window Ambiguity polynomial nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5023-L5031
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L5023-L5031

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology

theorem DimdPolyLEAN.windowAmbiguity_polynomial_nonzero
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    PKappa kappa ≠ 0 := by sorry
