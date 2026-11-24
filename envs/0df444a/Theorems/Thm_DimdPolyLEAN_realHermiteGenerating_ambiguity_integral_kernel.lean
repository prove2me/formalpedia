-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_kernel
-- name    : DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:12.659373+00:00
-- url     : https://prove2.me/theorems/658a6504-2c20-4b94-b42f-6ded79f8ada4
-- title:
--   Dimd Poly LEAN: real Hermite Generating ambiguity integral kernel
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating ambiguity integral kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L405-L430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L405-L430

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

theorem DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_kernel
    (x ω : ℝ) (u w : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        realHermiteGenerating (t - x / 2) w *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (u * w +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * u -
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ)) * w) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by sorry
