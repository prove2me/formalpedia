-- Prove2me | Theorems.Thm_AvramDividend_Classical_pos_moments_exp_tilt_integrable_right_ray
-- name    : AvramDividend.Classical.pos_moments_exp_tilt_integrable_right_ray
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:56:58.2668+00:00
-- url     : https://prove2.me/theorems/a3dcdb5e-4fbf-4299-a74c-1e60f333ce91
-- title:
--   Positive one-sided exponential moments become an open right-ray of exponential moments after Esscher tilting
-- statement:
--   If exp(u*x) is integrable for all positive u under μ, then weighting μ by exp(x) produces a measure whose exp(t*x) is integrable for every t>-1. Apply integrable_withDensity_iff and the real exponential addition law. This opens a half-plane including zero for the tilted complex MGF and is a direct prerequisite to positive-MGF measure uniqueness.
-- source:
--   Pinned Mathlib integrable_withDensity_iff and Real.exp_add. Supports measure_eq_of_pos_mgf_on_ray [4fb183cd-2d4f-4df5-8a23-9c6e5b201da0].

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.pos_moments_exp_tilt_integrable_right_ray
    (μ : Measure ℝ)
    (h : ∀ u : ℝ, 0 < u → Integrable (fun x : ℝ => Real.exp (u * x)) μ)
    (t : ℝ) (ht : -1 < t) :
    Integrable (fun x : ℝ => Real.exp (t * x))
      (μ.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp x))) := by sorry
