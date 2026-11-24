-- Prove2me | Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_memLp
-- name    : DimdPolyLEAN.complex_monomial_gaussian_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:10.450165+00:00
-- url     : https://prove2.me/theorems/fc806ced-d99d-47ba-9a2b-17edf4502b79
-- title:
--   Dimd Poly LEAN: complex monomial gaussian mem Lp
-- statement:
--   The Dimd Poly LEAN construction uses the complex monomial gaussian mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1015-L1036
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1015-L1036

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

theorem DimdPolyLEAN.complex_monomial_gaussian_memLp
    (k : ℕ) :
    MemLp (fun t : ℝ => (t : ℂ) ^ k *
      Complex.exp (-(((t : ℂ) ^ 2) / 2))) 2 (volume : Measure ℝ) := by sorry
