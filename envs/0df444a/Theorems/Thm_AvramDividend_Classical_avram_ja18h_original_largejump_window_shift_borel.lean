-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_largejump_window_shift_borel
-- name    : AvramDividend.Classical.avram_ja18h_original_largejump_window_shift_borel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:34:01.636775+00:00
-- url     : https://prove2.me/theorems/a3ae2dbc-5c52-4f4b-82b1-dbb78de5f0ab
-- title:
--   Original large negative jump window is a Borel functional of the shifted original path
-- statement:
--   For any s≤t, represent the original same-path signed large-negative jump integral on (s,t] by a Borel measurable functional J on the original future increment path. Account for marks exactly -1, the raw measure-count jump extractor, cadlag left limits, exact (0,t] minus (0,s] interval additivity and Proved negative-band shift identities 238b5785 and 613d1237. This is the sole nonalgebraic extraction needed for cutoff n=0; the compensated small band Ioc(-1,-1) is empty.
-- source:
--   AVRAM J-A18 genuine large mark path Borel extraction

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18h_original_largejump_window_shift_borel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ J : (ℝ≥0 → ℝ) → ℝ, Measurable J ∧
      ∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω -
          avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω =
        J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by sorry
