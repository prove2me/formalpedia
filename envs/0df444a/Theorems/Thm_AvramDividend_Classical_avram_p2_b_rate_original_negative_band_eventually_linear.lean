-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_negative_band_eventually_linear
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_negative_band_eventually_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:47:46.563311+00:00
-- url     : https://prove2.me/theorems/8f75624a-8a04-4058-a0d3-99baefcbc9a1
-- title:
--   Original Levy negative-band increment probability is eventually of order h
-- statement:
--   The original-process fourth exponential source derivative plus integrability implies a genuine O(h) negative-increment probability estimate on each band (-infinity,-epsilon], via lower bound of the fourth weight and Markov inequality. Assumes explicit measurability of original process marginals, without assuming any jump intensity identity. The conclusion controls ENNReal band probability multiplied by a strictly positive fourth-weight constant by h times the original Levy measure fourth-weight integral plus 1, eventually as h tends to 0 from the right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_increment_lintegral_markov_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_fourth_weight_real_lintegral_identification

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_negative_band_eventually_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ENNReal.ofReal ((1 - Real.exp (-θ * ε)) ^ 4) *
        P {ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
      ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := by sorry
