-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_compactly_supported_continuous_map
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_compactly_supported_continuous_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:47:15.362239+00:00
-- url     : https://prove2.me/theorems/9671a12b-10f6-4759-831d-b8f23370701b
-- title:
--   Original negative-mark test is represented by a genuine compactly supported continuous exponential-image test
-- statement:
--   Every continuous negative-mark test supported between finite lower and strictly negative upper cutoffs admits an exactly equal transformed test as a CompactlySupportedContinuousMap Real Real, namely g(z)=f(log z)/(z-1)^4. This packages the independently established real-line continuity and compact-support lemmas into the exact Mathlib interface needed for finite Borel-measure uniqueness via integration against compactly supported continuous maps.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_continuous_all_real
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_has_compact_support
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_compactly_supported_continuous_map
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    ∃ g : CompactlySupportedContinuousMap ℝ ℝ,
      ∀ z : ℝ, g z = f (Real.log z) / (z - 1) ^ 4 := by sorry
