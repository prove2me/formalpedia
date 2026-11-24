-- Prove2me | Theorems.Thm_DimdPolyLEAN_integral_real_pow_exp_neg_sq_of_even
-- name    : DimdPolyLEAN.integral_real_pow_exp_neg_sq_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:01.861372+00:00
-- url     : https://prove2.me/theorems/6cdde6e0-9857-4218-8477-d6e28b9da0e5
-- title:
--   Dimd Poly LEAN: integral real pow exp neg sq of even
-- statement:
--   The Dimd Poly LEAN construction uses the integral real pow exp neg sq of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1090-L1114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1090-L1114

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

theorem DimdPolyLEAN.integral_real_pow_exp_neg_sq_of_even
    {n : ℕ} (heven : Even n) :
    (∫ x : ℝ, x ^ n * Real.exp (-(x ^ (2 : ℕ)))) =
      Real.Gamma (((n : ℝ) + 1) / 2) := by sorry
