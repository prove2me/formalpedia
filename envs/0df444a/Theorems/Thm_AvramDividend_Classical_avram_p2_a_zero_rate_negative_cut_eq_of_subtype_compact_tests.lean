-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_negative_cut_eq_of_subtype_compact_tests
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_negative_cut_eq_of_subtype_compact_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:01:47.283688+00:00
-- url     : https://prove2.me/theorems/c7a9bd84-c620-434d-b87b-8d1df66025b0
-- title:
--   Negative real cutoff equality from finite-band subtype compact-test uniqueness
-- statement:
--   Transport measures on the negative real half-line through the measurable subtype embedding and invoke the proved Radon compact-test uniqueness theorem. Finite negative separated-band mass and subtype compact-test real integral equality imply exact equality of cutoff halfline mass, including potential atoms at the threshold.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_negative_band_compact_test_ext
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_negative_cut_eq_of_subtype_compact_tests
    (μ ν : Measure ℝ)
    (hμ : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) < ⊤)
    (hν : ∀ δ : ℝ, 0 < δ → ν (Iic (-δ)) < ⊤)
    (hTests : ∀ f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ,
      (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)) =
      (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) ν)))
    (ε : ℝ) (hε : 0 < ε) :
    μ (Iic (-ε)) = ν (Iic (-ε)) := by sorry
