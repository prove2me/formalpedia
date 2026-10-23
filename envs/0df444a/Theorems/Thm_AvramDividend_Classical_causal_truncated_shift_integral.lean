-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_truncated_shift_integral
-- name    : AvramDividend.Classical.causal_truncated_shift_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:19:04.88249+00:00
-- url     : https://prove2.me/theorems/70f65f60-1e03-4dac-b704-efda694ec634
-- title:
--   Removing the truncated causal input indicator after a positive time shift
-- statement:
--   For 0≤u≤x and any input g, integrating the time-windowed input g(t−u) over t∈(0,x] equals the primitive of g over (0,x−u]. Translate by u, intersect the shifted interval (−u,x−u] with the positive input window (0,x], and use set-integral indicator restriction. This is a core inner-integral reduction following Fubini for causal convolution.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_truncated_shift_integral
    (g : ℝ → ℝ) (u x : ℝ) (hu : 0 ≤ u) (hux : u ≤ x) :
    (∫ t in Ioc (0 : ℝ) x,
      ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
    (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) := by sorry
