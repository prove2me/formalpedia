-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_tilt_finite_of_integrable
-- name    : AvramDividend.Classical.exp_tilt_finite_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:00:44.799225+00:00
-- url     : https://prove2.me/theorems/96c82187-053f-416a-9a26-66c0bbeacdcf
-- title:
--   An integrable real exponential tilt produces a finite weighted measure
-- statement:
--   If exp(a*x) is integrable under a Borel measure μ, then the weighted measure withDensity(exp(a*x)) has finite total mass. This is the finiteness prerequisite for uniqueness via the complex MGF of an exponentially tilted measure.
-- source:
--   Mathlib isFiniteMeasure_withDensity_ofReal and Integrable.hasFiniteIntegral; prepares positive MGF uniqueness.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.exp_tilt_finite_of_integrable
    (μ : Measure ℝ) (a : ℝ)
    (h : Integrable (fun x : ℝ => Real.exp (a * x)) μ) :
    IsFiniteMeasure (μ.withDensity (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (a * x)))) := by sorry
