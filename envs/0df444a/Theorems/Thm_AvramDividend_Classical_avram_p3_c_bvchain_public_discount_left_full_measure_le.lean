-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_discount_left_full_measure_le
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_public_discount_left_full_measure_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:06:40.395633+00:00
-- url     : https://prove2.me/theorems/0eff3cc4-e1a4-4ee2-bfa6-6f3a03fa3de8
-- title:
--   Public generic full Stieltjes discount left-endpoint bound
-- statement:
--   For any real measure, nonnegative discount rate, and half-open interval, the full discounted lintegral of the interval, including singular-continuous mass and its right-endpoint atom, is bounded by the left-endpoint discount factor times the entire interval mass. This reusable Mathlib-only public bridge supports original BV source-frozen controlled dividend cells.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_public_discount_left_full_measure_le (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) :
    (∫⁻ t in Ioc a b, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * a))) * μ (Ioc a b) := by sorry
