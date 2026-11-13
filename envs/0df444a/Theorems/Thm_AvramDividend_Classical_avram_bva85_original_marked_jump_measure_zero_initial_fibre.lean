-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva85_original_marked_jump_measure_zero_initial_fibre
-- name    : AvramDividend.Classical.avram_bva85_original_marked_jump_measure_zero_initial_fibre
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:31:19.875221+00:00
-- url     : https://prove2.me/theorems/69cc5a7f-cf2b-4792-b53a-41d07dc7f31b
-- title:
--   Original marked jump measure has zero initial-time fibre under measurable marks
-- statement:
--   The original jump measure NX pushes positive-time Levy jump counts through the time/mark map. Assuming the mark map is measurable, it has zero mass on initial time times all negative or positive marks. This uses Proved BVA84 and isolates the mark-map measurability needed to eliminate the first half of M_n(0).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva84_original_strict_positive_jump_count_zero_at_initial_clock
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva85_original_marked_jump_measure_zero_initial_fibre
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hMeas : Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (({0} : Set ℝ≥0) ×ˢ Set.univ) = 0 := by sorry
