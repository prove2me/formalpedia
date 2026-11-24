-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_no_conj_interchange_of_finite_sum
-- name    : DimdPolyLEAN.realHermiteGenerating_no_conj_interchange_of_finite_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:47.175187+00:00
-- url     : https://prove2.me/theorems/74eac9a2-583d-4ebf-8e8b-3c959afc9528
-- title:
--   Dimd Poly LEAN: real Hermite Generating no conj interchange of finite sum
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating no conj interchange of finite sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1940-L1974
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L1940-L1974

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

theorem DimdPolyLEAN.realHermiteGenerating_no_conj_interchange_of_finite_sum
    (n m : ℕ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv m (realHermiteGenerating t) 0) =
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ, realHermiteGenerating t u * realHermiteGenerating t w) 0) 0 := by sorry
