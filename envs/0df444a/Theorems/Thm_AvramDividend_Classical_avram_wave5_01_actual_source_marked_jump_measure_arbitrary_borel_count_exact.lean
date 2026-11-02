-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:57:24.554895+00:00
-- url     : https://prove2.me/theorems/2c942e8f-b7ac-4d46-9808-101b8797d184
-- title:
--   Original source marked jump measure equals pathwise counting measure on every Borel time-mark set
-- statement:
--   For any original SpectrallyNegativeLevy P 𝓕 sample path ω and every Borel time-mark set A, the actual intrinsic N_X(ω,A) equals the en-cardinality of actual nonzero source jump times whose original time/size marks belong to A. No detached Poisson copy, no BV assumption, no almost-everywhere path exceptional set.
-- source:
--   Proved 9d68c5c2 joint source jumpmark measurability, Measure.map_apply, Measure.restrict_apply, Measure.count_apply on the exact original marked path map.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (A : Set (ℝ≥0 × ℝ)) (hA : MeasurableSet A) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) A =
    ({u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∈ A}).encard := by sorry
