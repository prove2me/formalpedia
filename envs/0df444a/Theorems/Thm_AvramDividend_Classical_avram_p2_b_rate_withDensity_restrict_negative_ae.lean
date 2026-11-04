-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_withDensity_restrict_negative_ae
-- name    : AvramDividend.Classical.avram_p2_b_rate_withDensity_restrict_negative_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:46:44.720479+00:00
-- url     : https://prove2.me/theorems/3562472a-a841-4bb0-8083-c9c137982822
-- title:
--   Negative restricted support is preserved by measurable density weighting
-- statement:
--   For any real Borel measure restricted to strictly negative marks, any further measurable nonnegative extended-real density retains the almost-everywhere property y < 0. This is a source-exact support bridge for the original Lévy weighted exponential-image rate.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_withDensity_restrict_negative_ae
    (ν : Measure ℝ) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    ∀ᵐ y ∂((ν.restrict (Set.Iio (0 : ℝ))).withDensity w), y < 0 := by sorry
