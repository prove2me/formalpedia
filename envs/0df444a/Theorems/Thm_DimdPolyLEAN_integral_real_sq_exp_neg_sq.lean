-- Prove2me | Theorems.Thm_DimdPolyLEAN_integral_real_sq_exp_neg_sq
-- name    : DimdPolyLEAN.integral_real_sq_exp_neg_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:36:59.180868+00:00
-- url     : https://prove2.me/theorems/f6e9e81e-7a44-425c-8031-cd7044c753b1
-- title:
--   Dimd Poly LEAN: integral real sq exp neg sq
-- statement:
--   The Dimd Poly LEAN construction uses the integral real sq exp neg sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L903-L927
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L903-L927

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

theorem DimdPolyLEAN.integral_real_sq_exp_neg_sq :
    (∫ x : ℝ, x ^ (2 : ℕ) * Real.exp (-(x ^ (2 : ℕ)))) = Real.sqrt Real.pi / 2 := by sorry
