-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_tilt_real_mgf_shift
-- name    : AvramDividend.Classical.exp_tilt_real_mgf_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:48:32.25255+00:00
-- url     : https://prove2.me/theorems/80bacfa0-f62f-4486-9f95-8ffc51b61f3f
-- title:
--   Real moment generating function under exponential measure tilt is the original MGF at a shifted argument
-- statement:
--   For any real Borel measure μ and real parameters a,s, weighting μ with exp(a x) shifts the real exponential integral from parameter s to a+s. Explicitly, ∫exp(sx)d(μ.withDensity(exp(ax))) = ∫exp((a+s)x)dμ. The formula holds even when either integral is not finite because Mathlib's Bochner integral-with-density identity accounts for integrability consistently. It is the exact analytic algebra step needed to convert positive one-sided MGFs into MGFs of a finite exponentially tilted measure on a right half-plane containing zero.
-- source:
--   Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap integral_withDensity_eq_integral_toReal_smul, Real.exp_add and ENNReal.toReal_ofReal. Prerequisite for measure_eq_of_pos_mgf_on_ray [4fb183cd-2d4f-4df5-8a23-9c6e5b201da0].

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.exp_tilt_real_mgf_shift
    (μ : Measure ℝ) (a s : ℝ) :
    (∫ x, Real.exp (s * x) ∂(μ.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x))))) =
    ∫ x, Real.exp ((a + s) * x) ∂μ := by sorry
