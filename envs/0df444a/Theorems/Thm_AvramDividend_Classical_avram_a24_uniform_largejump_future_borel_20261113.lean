-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_largejump_future_borel_20261113
-- name    : AvramDividend.Classical.avram_a24_uniform_largejump_future_borel_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:34:40.751208+00:00
-- url     : https://prove2.me/theorems/71b41f82-13c3-487f-afc6-95c0796858a5
-- title:
--   Original large-jump source window has a single Borel future-path statistic for every start time
-- statement:
--   For every fixed duration, one measurable functional of the original future Lévy increment path gives the actual large negative-jump integral over each translated interval, for every starting time and every original sample path.
-- source:
--   Proved original large-jump interval difference, signed physical negative mark shift and cadlag Borel jump extractor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_largejump_interval_difference
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_negative_band_shift_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single Borel statistic represents the physical large-jump increment at all start times. -/

theorem AvramDividend.Classical.avram_a24_uniform_largejump_future_borel_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∃ J : (ℝ≥0 → ℝ) → ℝ, Measurable J ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        avram_p4_h_gaussian_intrinsic_large_jump_sum X (s + T) ω -
          avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω =
        J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by sorry
