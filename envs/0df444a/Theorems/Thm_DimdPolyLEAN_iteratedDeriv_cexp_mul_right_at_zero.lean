-- Prove2me | Theorems.Thm_DimdPolyLEAN_iteratedDeriv_cexp_mul_right_at_zero
-- name    : DimdPolyLEAN.iteratedDeriv_cexp_mul_right_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:39.77289+00:00
-- url     : https://prove2.me/theorems/82077f36-79fe-4b4d-8caa-a190e8c05788
-- title:
--   Dimd Poly LEAN: iterated Deriv cexp mul right at zero
-- statement:
--   The Dimd Poly LEAN construction uses the iterated Deriv cexp mul right at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L713-L719
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L713-L719

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

theorem DimdPolyLEAN.iteratedDeriv_cexp_mul_right_at_zero (n : ℕ) (w : ℂ) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0 = w ^ n := by sorry
