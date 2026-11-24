-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_integral_mul_conj
-- name    : DimdPolyLEAN.realHermiteGenerating_integral_mul_conj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:35:33.215009+00:00
-- url     : https://prove2.me/theorems/d58026b1-944d-432c-b0ce-dae53079dfd0
-- title:
--   Dimd Poly LEAN: real Hermite Generating integral mul conj
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating integral mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L170-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L170-L174

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

theorem DimdPolyLEAN.realHermiteGenerating_integral_mul_conj (u w : ℂ) :
    (∫ t : ℝ, realHermiteGenerating t u * star (realHermiteGenerating t w)) =
      Complex.exp (u * star w) := by sorry
