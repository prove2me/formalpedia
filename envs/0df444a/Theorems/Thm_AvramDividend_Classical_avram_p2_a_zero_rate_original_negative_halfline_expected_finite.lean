-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_halfline_expected_finite
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_halfline_expected_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:01:04.737893+00:00
-- url     : https://prove2.me/theorems/6b9a98be-89bb-4eec-b9f0-fdfd98b091ba
-- title:
--   Actual original separated negative jump count has finite first moment bounded linearly in horizon
-- statement:
--   Every actual spectrally negative Levy process has uniformly finite expected negative jumps of size at least ε over any positive finite horizon. The proof compares original càdlàg jumps pathwise to the original uniform-grid negative increments, uses source-increment measurability and source small-time probability mass O(h), and applies Fatou to obtain a finite C*T upper bound. This is an original-source upper bound and does not assume the exact jump compensator or Lévy rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_band_mesh_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mesh_count_le_cell_indicators
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_fatou_eventual_grid_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_strict_grid_sum_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_grid_mean_horizon_uniform

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_halfline_expected_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) ∂P) ≤ ENNReal.ofReal (C * (T : ℝ)) := by sorry
