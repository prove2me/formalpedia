-- Prove2me | Theorems.Thm_DimdPolyLEAN_hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound
-- name    : DimdPolyLEAN.hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:22.714552+00:00
-- url     : https://prove2.me/theorems/d91f0b4a-6773-4997-9a3c-d3b61d8fcd80
-- title:
--   Dimd Poly LEAN: has Deriv At integral fixed mul shifted modulated real Hermite Generating right of bound
-- statement:
--   The Dimd Poly LEAN construction uses the has Deriv At integral fixed mul shifted modulated real Hermite Generating right of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L509-L570
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L509-L570

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

theorem DimdPolyLEAN.hasDerivAt_integral_fixed_mul_shifted_modulated_realHermiteGenerating_right_of_bound
    (phi : ℝ → ℂ) (x ω : ℝ) (w0 : ℂ) {s : Set ℂ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 w0)
    (hF_meas : ∀ᶠ z in 𝓝 w0,
      AEStronglyMeasurable
        (fun t : ℝ =>
          (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))
        (volume : Measure ℝ))
    (hF_int : Integrable
      (fun t : ℝ =>
        (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (hF'_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (volume : Measure ℝ))
    (h_bound : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ z : ℂ, z ∈ s →
      ‖(phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - z) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) z)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))‖ ≤
        bound t)
    (bound_integrable : Integrable bound (volume : Measure ℝ)) :
    HasDerivAt
      (fun z : ℂ => ∫ t : ℝ,
        (phi t * realHermiteGenerating (t - (1 / 2 : ℝ) * x) z) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      (∫ t : ℝ,
        (phi t *
            (((Real.sqrt 2 : ℂ) * ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) - w0) *
              realHermiteGenerating (t - (1 / 2 : ℝ) * x) w0)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ)))
      w0 := by sorry
