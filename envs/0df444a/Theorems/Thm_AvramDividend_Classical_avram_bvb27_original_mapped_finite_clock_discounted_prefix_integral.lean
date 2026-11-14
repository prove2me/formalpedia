-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_mapped_finite_clock_discounted_prefix_integral
-- name    : AvramDividend.Classical.avram_bvb27_original_mapped_finite_clock_discounted_prefix_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:06:58.433845+00:00
-- url     : https://prove2.me/theorems/c9367307-8ee8-4062-9bf8-f2070d2ac0df
-- title:
--   Original finite physical Lebesgue-to-NNReal time-clock map transports discounted strict-prefix integral exactly
-- statement:
--   For a finite nonnegative source physical time horizon T and any clipped endpoint b in [0,T], the true finite real Lebesgue clock restricted to the original Icc(0,T) and mapped to NNReal via Real.toNNReal integrates the strictly positive physical-time discounted exponential indicator for t<b exactly as the ordinary discounted real physical-time volume integral on Ioc(0,b). This is the exact measure-theoretic transport needed by the physical stopped negative-mark compensator K time integral and does not replace the original clock with a surrogate.
-- source:
--   Proved original finite source time-map preimage 24a903f6, mapped NNReal Ioc interval 18508f5d, pinned Mathlib integral_map, measurable_real_toNNReal, integral_indicator and setIntegral.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb27_original_mapped_finite_clock_discounted_prefix_integral
    (q T b : ℝ) (hT : 0 < T) (hb0 : 0 ≤ b) (hbT : b ≤ T) :
    (∫ t : ℝ≥0, (if 0 < t ∧ (t : ℝ) < b then
        Real.exp (-(q * (t : ℝ))) else 0)
      ∂(((volume : Measure ℝ).restrict (Icc (0 : ℝ) T)).map Real.toNNReal)) =
    (∫ t in Ioc (0 : ℝ) b,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by sorry
