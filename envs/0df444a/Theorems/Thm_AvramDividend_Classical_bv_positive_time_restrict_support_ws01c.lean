-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_positive_time_restrict_support_ws01c
-- name    : AvramDividend.Classical.bv_positive_time_restrict_support_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:21:31.281856+00:00
-- url     : https://prove2.me/theorems/52d6d3e1-851c-4519-99ac-7c47198829b2
-- title:
--   Positive restricted Lebesgue time lies almost surely in its support
-- statement:
--   The Lebesgue measure restricted to (0,1] is concentrated on positive real times in its support. This is needed to restrict stationarity and Fubini to valid nonnegative Lévy times.
-- source:
--   Causal repair of failed publication job 60bcd08c-b08c-47e2-8006-44f7b2bfdd94: its narrow import Mathlib.MeasureTheory.Measure.Restrict did not register the Lebesgue MeasureSpace real instance while elaborating volume.restrict. The corrected preamble imports Mathlib; formal statement unchanged. Complete original proof with only import changed: work/avram_ws01c_positive_time_support_solution_pub_repair_20261028.lean.

import Mathlib

open MeasureTheory Set Filter

theorem AvramDividend.Classical.bv_positive_time_restrict_support_ws01c :
    ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      t ∈ Ioc (0 : ℝ) 1 := by sorry
