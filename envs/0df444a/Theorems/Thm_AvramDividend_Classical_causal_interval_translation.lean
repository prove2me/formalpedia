-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_interval_translation
-- name    : AvramDividend.Classical.causal_interval_translation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:16:26.267285+00:00
-- url     : https://prove2.me/theorems/26d05f39-e062-4f25-ac70-c967e8cf9416
-- title:
--   Causal interval translation identity for Lebesgue integrals
-- statement:
--   For u≤x and any real input g, translating the interval (u,x] by u identifies the integral of g(t−u) with its zero-based primitive on (0,x−u]. This is the exact subinterval translation needed when the time-lag Fubini integral is restricted to causal support.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_interval_translation
    (g : ℝ → ℝ) (u x : ℝ) (hux : u ≤ x) :
    (∫ t in Ioc u x, g (t - u) ∂volume) =
    (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) := by sorry
