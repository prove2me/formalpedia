-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_mark_maps_any_horizon
-- name    : AvramDividend.Classical.avram_route_runner_f_original_frozen_mark_maps_any_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:23:24.879956+00:00
-- url     : https://prove2.me/theorems/60720000-91df-49fa-868a-92103fee517a
-- title:
--   Original and horizon-frozen Lévy jump mark maps measurable at arbitrary deterministic times
-- statement:
--   For every actual spectrally negative Lévy sample path and every nonnegative real time horizon, both its genuine original time-mark map and the time-mark map from the path frozen at the horizon are Borel measurable. Extends the existing integer-horizon source proof exactly to the fractional equal-cell boundaries used by the original marked-product expectation factorisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_f_original_frozen_mark_maps_any_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    Measurable (fun u : ℝ≥0 => (u, X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ∧
    Measurable (fun u : ℝ≥0 => (u, X.X (min u T) ω -
      Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u)) := by sorry
