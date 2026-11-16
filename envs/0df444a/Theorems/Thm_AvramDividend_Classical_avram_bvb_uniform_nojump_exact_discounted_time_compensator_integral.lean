-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_uniform_nojump_exact_discounted_time_compensator_integral
-- name    : AvramDividend.Classical.avram_bvb_uniform_nojump_exact_discounted_time_compensator_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:11:02.124819+00:00
-- url     : https://prove2.me/theorems/4a76dc01-0da2-458d-be38-56683918fd01
-- title:
--   Unit-discount original Lévy zero-contact compensator time integral equals one minus terminal exponential
-- statement:
--   For every real horizon T, the exact discounted time integral from 0 to T at unit discount equals 1−exp(−T). This is the analytic bridge needed to identify the original finite negative-jump uniform rate-one zero-reserve compensation term K=(1/2)(1−exp(−T)) and explain the strict pathwise cash deficit when K is omitted.
-- source:
--   Use pinned Mathlib intervalIntegral.integral_comp_neg to reverse the integration time, and pinned integral_exp fundamental theorem to evaluate exp at the endpoints, with no probabilistic assumptions.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open MeasureTheory intervalIntegral Real

theorem AvramDividend.Classical.avram_bvb_uniform_nojump_exact_discounted_time_compensator_integral (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t)) =
      1 - Real.exp (-T) := by sorry
