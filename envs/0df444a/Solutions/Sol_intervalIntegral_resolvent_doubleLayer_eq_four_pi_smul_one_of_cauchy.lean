-- Prove2me | solution 1 for intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:09.88377+00:00
-- url     : https://prove2.me/submissions/8d8e0cc0-4e55-4f30-98a7-c7b2ada79bf4

import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Theorems.Thm_ContinuousLinearMap_intervalIntegral_add_adjoint

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (gamma : ℝ → ℂ)
    (hint : IntervalIntegrable
      (fun t ↦ deriv gamma t • resolvent A (gamma t)) volume 0 (2 * Real.pi))
    (hCauchy : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv gamma t • resolvent A (gamma t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E)) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      ((-I * deriv gamma t) • resolvent A (gamma t)) +
        ContinuousLinearMap.adjoint
          ((-I * deriv gamma t) • resolvent A (gamma t))) =
      (4 * Real.pi) • (1 : E →L[ℂ] E) := by
  let B : ℝ → E →L[ℂ] E := fun t ↦
    (-I * deriv gamma t) • resolvent A (gamma t)
  have hBfun : B = fun t ↦ (-I) • (deriv gamma t • resolvent A (gamma t)) := by
    funext t
    simp only [B, smul_smul]
  have hB : IntervalIntegrable B volume 0 (2 * Real.pi) := by
    rw [hBfun]
    exact ⟨hint.1.smul_enorm (-I), hint.2.smul_enorm (-I)⟩
  have hBint : (∫ t in (0 : ℝ)..(2 * Real.pi), B t) =
      (2 * Real.pi) • (1 : E →L[ℂ] E) := by
    rw [hBfun, intervalIntegral.integral_smul, hCauchy, smul_smul]
    congr 1
    have hI : I * (2 * ((Real.pi : ℂ) * I)) = -(2 * (Real.pi : ℂ)) := by
      calc
        I * (2 * ((Real.pi : ℂ) * I)) = (2 * (Real.pi : ℂ)) * (I * I) := by ring
        _ = -(2 * (Real.pi : ℂ)) := by rw [I_mul_I, mul_neg, mul_one]
    calc
      -I * (2 * (Real.pi : ℂ) * I) = -(I * (2 * ((Real.pi : ℂ) * I))) := by ring
      _ = -(-(2 * (Real.pi : ℂ))) := congrArg Neg.neg hI
      _ = (((2 * Real.pi : ℝ) : ℂ)) := by norm_num
  change (∫ t in (0 : ℝ)..(2 * Real.pi),
      B t + ContinuousLinearMap.adjoint (B t)) = _
  rw [ContinuousLinearMap.intervalIntegral_add_adjoint hB, hBint]
  have hadj : ContinuousLinearMap.adjoint
      ((2 * Real.pi) • (1 : E →L[ℂ] E)) =
      (2 * Real.pi) • (1 : E →L[ℂ] E) := by
    change ContinuousLinearMap.adjoint
      (((2 * Real.pi : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
      (((2 * Real.pi : ℝ) : ℂ) • (1 : E →L[ℂ] E))
    rw [map_smulₛₗ, Complex.conj_ofReal, ContinuousLinearMap.adjoint_one]
  rw [hadj, ← add_smul]
  congr 1
  ring
