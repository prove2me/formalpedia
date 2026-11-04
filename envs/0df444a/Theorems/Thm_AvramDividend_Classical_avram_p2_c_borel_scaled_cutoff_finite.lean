-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_scaled_cutoff_finite
-- name    : AvramDividend.Classical.avram_p2_c_borel_scaled_cutoff_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:29:48.173145+00:00
-- url     : https://prove2.me/theorems/c3af6df9-7083-4b73-ac8c-3dc82681f20f
-- title:
--   Finite Lévy-time scaling preserves ENNReal Borel cutoff finiteness
-- statement:
--   If a Borel measure has finite mass on a lower half-line, multiplying that measure by any finite nonnegative time duration preserves finite mass on that half-line. This supplies the finite comparison measure needed when instantiating original expected-count versus time-scaled Lévy intensity measure-uniqueness interfaces.
-- source:
--   Pinned Mathlib ENNReal.mul_ne_top, coe_ne_top and scalar measure evaluation; independent of stochastic rate or source analytics.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_scaled_cutoff_finite
    (ν : Measure ℝ) (c : ℝ) (hνfin : ν (Iic c) ≠ ⊤)
    (T : ℝ≥0) :
    (((T : ℝ≥0∞) • ν) (Iic c)) ≠ ⊤ := by sorry
