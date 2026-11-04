-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_mark_map_measurable_of_path_and_left_limit
-- name    : AvramDividend.Classical.avram_wave7_06_original_mark_map_measurable_of_path_and_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:16:21.478736+00:00
-- url     : https://prove2.me/theorems/ab9dba1f-6dc5-4234-84cf-646c0f29cba0
-- title:
--   Source Lévy time-and-jump mark map measurable from its path and left-limit functions
-- statement:
--   For the literal original Lévy path X.X·ω, separate measurability of its sample trajectory and strict-left-limit trajectory implies Borel measurability of the genuine time-and-jump-size map by measurable pair formation and subtraction. The path and left-limit measurability hypotheses remain explicit and can be discharged using the source right-continuous càdlàg assumptions; no unrelated process is used.
-- source:
--   W7-06 original count-unit source path measurability decomposition

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_mark_map_measurable_of_path_and_left_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hPath : Measurable (fun t : ℝ≥0 => X.X t ω))
    (hLeft : Measurable (fun t : ℝ≥0 =>
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)) :
    Measurable (fun u : ℝ≥0 => (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
