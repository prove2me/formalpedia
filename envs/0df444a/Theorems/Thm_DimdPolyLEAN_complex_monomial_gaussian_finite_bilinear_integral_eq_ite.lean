-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_finite_bilinear_integral_eq_ite
-- name    : DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_ite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:17:14.411221+00:00
-- url     : https://prove2.me/theorems/6d97af0f-a7de-4245-98dd-c2174a3d5d34
-- title:
--   Dimd Poly LEAN: complex monomial gaussian finite bilinear integral eq ite
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian finite bilinear integral eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1206-L1230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1206-L1230

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

theorem DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integral_eq_ite
    (s t : Finset ℕ) (a b : ℕ → ℂ) :
    (∫ x : ℝ,
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (complexMonomialGaussian k x *
            complexMonomialGaussian l x)) =
      ∑ k ∈ s, ∑ l ∈ t,
        (a k * b l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0) := by sorry
