-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_finite_bilinear_integral_eq_zero_of_odd
-- name    : DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_zero_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:37:52.463795+00:00
-- url     : https://prove2.me/theorems/4e7cf85a-a4f6-4bdb-a692-fafd01978047
-- title:
--   Dimd Poly LEAN: complex monomial gaussian finite bilinear integral eq zero of odd
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian finite bilinear integral eq zero of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1232-L1242
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1232-L1242

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

theorem DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_zero_of_odd
    (s t : Finset ℕ) (a b : ℕ → ℂ)
    (hodd : ∀ k ∈ s, ∀ l ∈ t, Odd (k + l)) :
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) = 0 := by sorry
