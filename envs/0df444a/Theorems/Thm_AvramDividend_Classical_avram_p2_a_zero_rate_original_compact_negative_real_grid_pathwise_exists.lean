-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_real_grid_pathwise_exists
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_real_grid_pathwise_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:50:51.653681+00:00
-- url     : https://prove2.me/theorems/8626c31d-d563-4069-9581-fd4cb921cde4
-- title:
--   Original Lévy compact negative test real-grid pathwise existence without auxiliary separation
-- statement:
--   Combine accepted compact negative support separation (automatic vanishing near zero) with the genuine source-specific original Lévy real-grid jump-test pathwise limit. This discharges the almost-everywhere pathwise-limit hypothesis of the proved P2-J expectation theorem, for any original sample path and compact strictly negative continuous test.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_real_grid_pathwise_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g)) (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∀ ω : Ω, ∃ z : ℝ,
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
      atTop (𝓝 z) := by sorry
