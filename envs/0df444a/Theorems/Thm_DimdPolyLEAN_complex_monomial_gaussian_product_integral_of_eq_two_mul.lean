-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_product_integral_of_eq_two_mul
-- name    : DimdPolyLEAN.complex_monomial_gaussian_product_integral_of_eq_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:37:44.702905+00:00
-- url     : https://prove2.me/theorems/195c5749-4260-43e5-aab1-b9de66f2c072
-- title:
--   Dimd Poly LEAN: complex monomial gaussian product integral of eq two mul
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian product integral of eq two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1154-L1167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1154-L1167

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
open scoped Nat

theorem DimdPolyLEAN.complex_monomial_gaussian_product_integral_of_eq_two_mul
    {k l r : ℕ} (hkl : k + l = 2 * r) :
    (∫ t : ℝ,
      complexMonomialGaussian k t * complexMonomialGaussian l t) =
      (((((2 * r - 1 : ℕ)‼ : ℕ) : ℝ) * Real.sqrt Real.pi /
        (2 ^ r : ℝ)) : ℂ) := by sorry
