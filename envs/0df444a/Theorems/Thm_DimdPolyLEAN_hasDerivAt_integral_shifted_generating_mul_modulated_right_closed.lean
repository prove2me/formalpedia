-- Prove2me | Theorems.Thm_DimdPolyLEAN_hasDerivAt_integral_shifted_generating_mul_modulated_right_closed
-- name    : DimdPolyLEAN.hasDerivAt_integral_shifted_generating_mul_modulated_right_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:30.648584+00:00
-- url     : https://prove2.me/theorems/70dac973-c3c1-4b6c-886c-5ad590734795
-- title:
--   Dimd Poly LEAN: has Deriv At integral shifted generating mul modulated right closed
-- statement:
--   The Dimd Poly LEAN construction uses the has Deriv At integral shifted generating mul modulated right closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L625-L667
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L625-L667

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

theorem DimdPolyLEAN.hasDerivAt_integral_shifted_generating_mul_modulated_right_closed
    (u w0 : ℂ) (x ω : ℝ) :
    HasDerivAt
      (fun w : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ)))
      (((u -
          star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
          Complex.exp
            (u * w0 +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w0)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))
      w0 := by sorry
