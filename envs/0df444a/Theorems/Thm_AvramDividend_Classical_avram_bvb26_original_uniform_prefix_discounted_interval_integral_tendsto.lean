-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_uniform_prefix_discounted_interval_integral_tendsto
-- name    : AvramDividend.Classical.avram_bvb26_original_uniform_prefix_discounted_interval_integral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:56:40.248491+00:00
-- url     : https://prove2.me/theorems/fb4a3f35-a69a-46b1-b3a2-0f09c63618eb
-- title:
--   Original physical uniform-grid clipped-prefix discounted Lebesgue integral converges to full finite horizon
-- statement:
--   For every physical horizon T strictly positive and discount parameter q, the actual BV source uniform-grid clipped prefix T-T/(n+2) increases towards T. The continuous physical exponential discounted volume integral over the real-time interval from zero to this exact clipped prefix converges to the same discounted volume integral over the full original finite horizon. This is the terminal-limit analytic bridge needed for the stopped negative-mark K compensator on original all-zero reserve survival paths. No distributional, probabilistic or alternative grid assumptions are introduced.
-- source:
--   Pinned Mathlib intervalIntegral.continuous_primitive and Continuous.intervalIntegrable, original physical source uniform grid from ed067740 and accepted a91aa28a.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb26_original_uniform_prefix_discounted_interval_integral_tendsto
    (q T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      ∫ t in (0 : ℝ)..(T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))
      atTop (𝓝 (∫ t in (0 : ℝ)..T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))) := by sorry
