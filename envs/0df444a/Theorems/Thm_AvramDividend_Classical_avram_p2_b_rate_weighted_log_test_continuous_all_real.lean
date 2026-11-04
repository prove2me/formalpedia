-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_continuous_all_real
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_all_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:34:43.465891+00:00
-- url     : https://prove2.me/theorems/cd7cb408-b7a7-4cf9-a17b-814ce2f92367
-- title:
--   Full real-line continuity of inverse weighted logarithmic compact-negative test
-- statement:
--   If f is continuous and vanishes below a finite mark a and above a strictly negative mark -epsilon, then g(z)=f(log z)/(z-1)^4 is continuous on the entire real line. At zero, Real.log_abs and the lower cutoff force g to vanish on a two-sided neighbourhood; at one, the previously Proved endpoint-one vanishing lemma applies; elsewhere ordinary composition and division are continuous. Together with the independently Proved compact-support theorem this makes g a genuine continuous compactly supported real test suitable for finite-measure uniqueness.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_all_real
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Continuous (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) := by sorry
