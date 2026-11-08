-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_weighted_cutoff_any_horizon
-- name    : AvramDividend.Classical.avram_route_runner_f_original_frozen_weighted_cutoff_any_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:36:48.621621+00:00
-- url     : https://prove2.me/theorems/8270d6dd-3f4f-445a-93c1-212d06d269b5
-- title:
--   Original intrinsic weighted negative-jump prefix mass is preserved by arbitrary-time freezing
-- statement:
--   On every genuine original spectrally negative Lévy sample path, freezing at any nonnegative deterministic horizon preserves the strict cutoff negative marked-jump weighted integral in the exact half-open time window. This is the fractional-horizon source-locality identity needed to show the original physical short-cell products are filtration-measurable and independent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_strict_negative_cutoff_mark_weight_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_mark_maps_any_horizon
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_generic_marked_window_count_any_horizon

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_f_original_frozen_weighted_cutoff_any_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u)))) := by sorry
