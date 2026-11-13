-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva88_original_marked_jump_zero_initial_fibre_without_meas_assumption
-- name    : AvramDividend.Classical.avram_bva88_original_marked_jump_zero_initial_fibre_without_meas_assumption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:37:43.171186+00:00
-- url     : https://prove2.me/theorems/fb6c1c6a-2b87-43ce-837f-43a7913e4399
-- title:
--   Original marked Lévy jump measure zero at initial time unconditionally from source process
-- statement:
--   For every original spectrally negative Lévy process and path, its marked jump measure assigns zero mass to initial time times all marks, with no additional mark-map measurability hypothesis. Proved route runner supplies that source measurability; Proved BVA85 gives the mapped count-null result. Directly applicable to BVA63 initial signed source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_mark_maps_any_horizon
import Theorems.Thm_AvramDividend_Classical_avram_bva85_original_marked_jump_measure_zero_initial_fibre
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva88_original_marked_jump_zero_initial_fibre_without_meas_assumption
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (({0} : Set ℝ≥0) ×ˢ Set.univ) = 0 := by sorry
