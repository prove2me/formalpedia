-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_product_integral_of_even
-- name    : DimdPolyLEAN.complex_monomial_gaussian_product_integral_of_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:48.425586+00:00
-- url     : https://prove2.me/theorems/33dfb9a9-d71c-4b26-a56f-722e6c03a351
-- title:
--   Dimd Poly LEAN: complex monomial gaussian product integral of even
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian product integral of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1116-L1151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1116-L1151

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

theorem DimdPolyLEAN.complex_monomial_gaussian_product_integral_of_even
    {k l : ℕ} (heven : Even (k + l)) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ) := by sorry
