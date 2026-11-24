-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_hasDerivAt
-- name    : DimdPolyLEAN.realHermiteGenerating_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:44.557805+00:00
-- url     : https://prove2.me/theorems/e08f8eb3-58f9-4887-9a45-fb49ab921715
-- title:
--   Dimd Poly LEAN: real Hermite Generating has Deriv At
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L110-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L110-L130

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

theorem DimdPolyLEAN.realHermiteGenerating_hasDerivAt (t : ℝ) (u : ℂ) :
    HasDerivAt (realHermiteGenerating t)
      (((Real.sqrt 2 : ℂ) * (t : ℂ) - u) * realHermiteGenerating t u) u := by sorry
