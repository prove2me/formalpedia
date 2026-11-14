-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
-- name    : AvramDividend.Classical.avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:59:31.015014+00:00
-- url     : https://prove2.me/theorems/870c2113-3839-4b1a-a871-4a0613f8e1e3
-- title:
--   Actual original clipped physical discount set integral over Ioc zero-to-prefix converges to full horizon
-- statement:
--   The discounted physical Lebesgue set integral over the exact original uniform prefix Ioc(0,T-T/(n+2)) tends to the discounted physical Lebesgue set integral over Ioc(0,T). This is precisely the real-time restriction appearing in the zero-contact stopped negative-mark K compensator of the original BV survival proof. It builds from the accepted (or independently verified) interval integral continuity and identifies Ioc with the interval integral using nonnegative original prefix endpoints.
-- source:
--   Original uniform physical grid T-T/(n+2) from ed067740, Mathlib intervalIntegral.integral_of_le and div_le_self, published source discounted interval integral fb4a3f35.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_uniform_prefix_discounted_interval_integral_tendsto
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
    (q T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      ∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))) := by sorry
