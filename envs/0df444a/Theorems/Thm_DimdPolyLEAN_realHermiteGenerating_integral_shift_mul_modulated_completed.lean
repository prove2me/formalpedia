-- Prove2me | Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_integral_shift_mul_modulated_completed
-- name    : DimdPolyLEAN.realHermiteGenerating_integral_shift_mul_modulated_completed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:52.203773+00:00
-- url     : https://prove2.me/theorems/3f4240f7-511c-4294-84f8-4fb2ef093659
-- title:
--   Dimd Poly LEAN: real Hermite Generating integral shift mul modulated completed
-- statement:
--   The Dimd Poly LEAN construction uses the real Hermite Generating integral shift mul modulated completed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L234-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L234-L244

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

theorem DimdPolyLEAN.realHermiteGenerating_integral_shift_mul_modulated_completed
    (u v : ℂ) (x ω : ℝ) :
    (∫ t : ℝ,
      realHermiteGenerating t u * realHermiteGenerating (t - x) v *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        ((-((x : ℂ) ^ 2) / 2 - (Real.sqrt 2 : ℂ) * (x : ℂ) * v -
            (u ^ 2 + v ^ 2) / 2) +
          (((x : ℂ) + (Real.sqrt 2 : ℂ) * (u + v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4) := by sorry
