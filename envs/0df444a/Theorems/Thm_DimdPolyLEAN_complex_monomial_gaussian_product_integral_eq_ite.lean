-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_product_integral_eq_ite
-- name    : DimdPolyLEAN.complex_monomial_gaussian_product_integral_eq_ite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:23:02.501804+00:00
-- url     : https://prove2.me/theorems/27a38d51-e699-4fe3-863c-4f87170a1250
-- title:
--   Dimd Poly LEAN: complex monomial gaussian product integral eq ite
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian product integral eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1169-L1179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1169-L1179

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

theorem DimdPolyLEAN.complex_monomial_gaussian_product_integral_eq_ite
    (k l : ℕ) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      if Even (k + l) then
        (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
      else 0 := by sorry
