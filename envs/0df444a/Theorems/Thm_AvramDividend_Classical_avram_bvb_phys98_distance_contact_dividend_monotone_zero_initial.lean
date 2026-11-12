-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys98_distance_contact_dividend_monotone_zero_initial
-- name    : AvramDividend.Classical.avram_bvb_phys98_distance_contact_dividend_monotone_zero_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:30:52.748821+00:00
-- url     : https://prove2.me/theorems/e25666f0-91c7-4972-b88c-6d4c28f406c2
-- title:
--   Distance-contact deterministic dividend is monotone and starts at zero
-- statement:
--   For any contact set, the distance-profile dividend function has zero initial value and is nondecreasing because distance to a set is one-Lipschitz. This is a needed admissibility ingredient for the physical BV grid counterexample.
-- source:
--   Original BV phys95 contact-set counterexample prerequisite

import Mathlib
open Set

theorem AvramDividend.Classical.avram_bvb_phys98_distance_contact_dividend_monotone_zero_initial (F : Set ℝ) : Monotone (fun t : ℝ => t + Metric.infDist t F - Metric.infDist 0 F) ∧ ((0 : ℝ) + Metric.infDist 0 F - Metric.infDist 0 F) = 0 := by sorry
