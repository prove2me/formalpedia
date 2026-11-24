-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_conj_kernel
-- name    : DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_conj_kernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:36:11.690638+00:00
-- url     : https://prove2.me/theorems/964e7bff-3ef5-43d0-8313-f0b3e299dd0f
-- title:
--   Dimd Poly LEAN: real Hermite Generating ambiguity integral conj kernel
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating ambiguity integral conj kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L448-L474
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L448-L474

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

theorem DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_conj_kernel
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        star (realHermiteGenerating (t - x / 2) v) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (u * star v +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * u -
          (((x : ℂ) + (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * star v) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by sorry
