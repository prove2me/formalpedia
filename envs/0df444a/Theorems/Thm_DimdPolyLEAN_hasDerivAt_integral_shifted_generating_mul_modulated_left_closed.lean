-- Prove2me | Theorems.Thm_DimdPolyLEAN_hasDerivAt_integral_shifted_generating_mul_modulated_left_closed
-- name    : DimdPolyLEAN.hasDerivAt_integral_shifted_generating_mul_modulated_left_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:37.035189+00:00
-- url     : https://prove2.me/theorems/48b47bf6-322a-42ea-80ca-b68e19acf159
-- title:
--   Dimd Poly LEAN: has Deriv At integral shifted generating mul modulated left closed
-- statement:
--   The Dimd Poly LEAN construction uses the has Deriv At integral shifted generating mul modulated left closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L669-L711
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean#L669-L711

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

theorem DimdPolyLEAN.hasDerivAt_integral_shifted_generating_mul_modulated_left_closed
    (u0 w : ℂ) (x ω : ℝ) :
    HasDerivAt
      (fun u : ℂ => ∫ t : ℝ,
        realHermiteGenerating (t + x / 2) u *
          realHermiteGenerating (t - x / 2) w *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (ω * t : ℂ)))
      (((w +
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
          Complex.exp
            (u0 * w +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u0 -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))
      u0 := by sorry
