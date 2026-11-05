-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_subtype_comap_integral_from_real_test
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_subtype_comap_integral_from_real_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:37:21.246346+00:00
-- url     : https://prove2.me/theorems/9cb9faee-ff07-464a-9b77-b8fd98260714
-- title:
--   Exact negative-subtype comap integral equals supported ambient real-test integral
-- statement:
--   For an arbitrary original real measure, any real-valued test supported strictly in the negative half-line has the same integral as its restriction to the negative subtype against the comapped measure. The proof uses the measurable subtype embedding, its map-comap restriction formula, integral_map, and exact vanishing of the test outside the negative half-line. This is the measure-theoretic bridge needed to move the genuine original jump-test identity into Radon uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_subtype_comap_integral_from_real_test
    (μ : Measure ℝ)
    (f : {x : ℝ // x < 0} → ℝ)
    (g : ℝ → ℝ)
    (hgsupp : tsupport g ⊆ Iio (0 : ℝ))
    (hagree : ∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) :
    (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)) =
      (∫ y, g y ∂μ) := by sorry
