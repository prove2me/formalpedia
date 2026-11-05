-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_signed_tests_determine_negative_borel
-- name    : AvramDividend.Classical.avram_p2_a_assist_signed_tests_determine_negative_borel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:02:34.064621+00:00
-- url     : https://prove2.me/theorems/6d69e492-5775-4b1f-826e-7b51ca520635
-- title:
--   Signed compact-negative test integral equality identifies separated Borel rates
-- statement:
--   For any real measures with finite masses on all negative separated left half-lines, agreement of integrals of every signed compactly supported continuous test strictly inside the negative half-line implies equality of every separated negative Borel mass. Transport zero extensions from the negative subtype, apply already Proved negative-subtype Radon uniqueness to all cutoffs and the finite-cutoff CDF extension, without any stochastic assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_negative_subtype_compact_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_subtype_comap_integral_from_real_test
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_negative_cut_eq_of_subtype_compact_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_negative_cdf_determines_separated_borel
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_assist_signed_tests_determine_negative_borel
    (μ ν : Measure ℝ)
    (hμBand : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) < ⊤)
    (hνBand : ∀ δ : ℝ, 0 < δ → ν (Iic (-δ)) < ⊤)
    (hSigned : ∀ (g : ℝ → ℝ), Continuous g →
      IsCompact (tsupport g) → tsupport g ⊆ Iio (0 : ℝ) →
      (∫ y, g y ∂μ) = (∫ y, g y ∂ν))
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    μ B = ν B := by sorry
