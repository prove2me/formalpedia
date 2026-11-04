-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_interval_mass_clipped
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_clock_interval_mass_clipped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:45:47.002735+00:00
-- url     : https://prove2.me/theorems/c844d12c-7780-48fc-9c3b-c545a60b5271
-- title:
--   Original finite physical clock interval mass clips exactly at T for every interval
-- statement:
--   The genuine nonnegative physical clock obtained by restricting real Lebesgue measure to [0,T] and mapping by Real.toNNReal assigns every (s,t] the same mass as (s,min(t,T)], with no ordering assumptions on s,t,T. This is measure-theoretic physical-clock clipping, including crossing-horizon and after-horizon cases, and supports proving original X.ν marked compensator equality for all adapted finite cells.
-- source:
--   Proved source P3-B time-preimage clipping; Mathlib Measure.map_apply and Measure.restrict_apply.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_preimage_clipped_Ioc
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_clock_interval_mass_clipped
    (s t T : ℝ≥0) :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s t) =
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s (min t T)) := by sorry
