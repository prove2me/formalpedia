-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_product_integrable
-- name    : DimdPolyLEAN.complex_monomial_gaussian_product_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:57.045081+00:00
-- url     : https://prove2.me/theorems/9311ada2-ebfe-421d-a419-1d8a7c75f79c
-- title:
--   Dimd Poly LEAN: complex monomial gaussian product integrable
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian product integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1042-L1055
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1042-L1055

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

theorem DimdPolyLEAN.complex_monomial_gaussian_product_integrable
    (k l : ℕ) :
    Integrable
      (fun t : ℝ =>
        complexMonomialGaussian k t * complexMonomialGaussian l t)
      (volume : Measure ℝ) := by sorry
