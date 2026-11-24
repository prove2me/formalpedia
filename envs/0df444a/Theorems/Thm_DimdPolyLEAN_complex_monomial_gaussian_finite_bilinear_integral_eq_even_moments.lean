-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_finite_bilinear_integral_eq_even_moments
-- name    : DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_even_moments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:38:05.40458+00:00
-- url     : https://prove2.me/theorems/4eb82f8b-042c-4709-9f32-b89e09ff21f7
-- title:
--   Dimd Poly LEAN: complex monomial gaussian finite bilinear integral eq even moments
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian finite bilinear integral eq even moments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1244-L1256
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1244-L1256

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

theorem DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_even_moments
    (s t : Finset ℕ) (a b : ℕ → ℂ)
    (heven : ∀ k ∈ s, ∀ l ∈ t, Even (k + l)) :
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) =
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ) := by sorry
