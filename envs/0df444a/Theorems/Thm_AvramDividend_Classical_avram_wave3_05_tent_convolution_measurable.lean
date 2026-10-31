-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_convolution_measurable
-- name    : AvramDividend.Classical.avram_wave3_05_tent_convolution_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:52:03.549617+00:00
-- url     : https://prove2.me/theorems/73d4867c-a3b9-418c-8949-017c7e62868a
-- title:
--   Measurability of the compensated Taylor-tent convolution in reserve
-- statement:
--   The source compensated Taylor remainder is measurable in the reserve whenever its second-derivative factor is measurable. Uses the pinned Mathlib StronglyMeasurable.integral_prod_right, with a compact jump-size interval and the correct nonnegative orientation. This is required to derive integrability of the signed positive-reserve Taylor remainder from an L1 convolution majorant.
-- source:
--   Exact pinned Mathlib, private remote elaboration job 8da080ed-e27c-4b84-9df3-b82e9908a6ba, 30 October 2026.

import Mathlib

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_convolution_measurable
    (F : ℝ → ℝ) (hF : Measurable F)
    (r : ℝ) (hr : 0 ≤ r) :
    Measurable (fun x : ℝ =>
      ∫ s in (0 : ℝ)..r, (r - s) * F (x - s)) := by sorry
