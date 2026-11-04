-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
-- name    : AvramDividend.Classical.avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:08:56.072335+00:00
-- url     : https://prove2.me/theorems/0a4c69be-543d-42be-b358-bbb36918df78
-- title:
--   Original nonzero jump time set Borel measurable from original mark map
-- statement:
--   If the literal source X time-and-jump-size map is measurable along the fixed path ω, then the strictly positive jump-time set of X is measurable, by taking the preimage of the real complement of the singleton zero under the second projection and intersecting with (0,∞). No other process or probability space is used.
-- source:
--   Wave7-06 source counting unit; removes the redundant jump-set measurability premise

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hMark : Measurable
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) :
    MeasurableSet {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by sorry
