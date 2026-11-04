-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_compact_negative_jump_mean
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_uncentered_compact_negative_jump_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:42:43.402218+00:00
-- url     : https://prove2.me/theorems/ceeb5f73-e74f-4f17-9327-5a61254e35db
-- title:
--   Original intrinsic negative compact-test jump sum has the original Levy measure expectation
-- statement:
--   For the actual original spectrally negative Levy process, show that every compactly supported continuous real test with support strictly below zero has an integrable finite intrinsic jump-sum over a positive time interval. The finite set consists of exactly the original uncentred left-limit jumps at which the test is nonzero, and its real Bochner expectation equals the horizon times the test integral against the original negative Levy measure. No separately hypothesised rate, compensator, mesh limit or auxiliary process is introduced.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_jump_sum_mean_of_smalltime_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_negative_test_real_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_jump_equals_centered_jump

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_uncentered_compact_negative_jump_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u)) ∧
      (∫ ω, J ω ∂P) = (T : ℝ) *
        (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ)))) := by sorry
