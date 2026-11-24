-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_finite_bilinear_integrable
-- name    : DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:37:48.713814+00:00
-- url     : https://prove2.me/theorems/cb770fb0-02c4-4166-9361-629e66a01c5b
-- title:
--   Dimd Poly LEAN: complex monomial gaussian finite bilinear integrable
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian finite bilinear integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1193-L1204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1193-L1204

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

theorem DimdPolyLEAN.complex_monomial_gaussian_finite_bilinear_integrable
    (s t : Finset ℕ) (a b : ℕ → ℂ) :
    Integrable
      (fun x : ℝ =>
        ∑ k ∈ s, ∑ l ∈ t,
          (a k * b l) *
            (complexMonomialGaussian k x *
              complexMonomialGaussian l x))
      (volume : Measure ℝ) := by sorry
