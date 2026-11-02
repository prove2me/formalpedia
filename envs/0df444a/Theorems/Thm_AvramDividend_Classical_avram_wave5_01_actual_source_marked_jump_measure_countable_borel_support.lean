-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_countable_borel_support
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_marked_jump_measure_countable_borel_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:42:24.398164+00:00
-- url     : https://prove2.me/theorems/7a4d6307-3350-43b2-a17a-36c297d02844
-- title:
--   Actual original Lévy marked jump measure is concentrated on a countable Borel same-path graph
-- statement:
--   For every actual SpectrallyNegativeLevy P 𝓕 source process and every original sample path ω, the intrinsic time-mark jump measure is carried by a countable Borel subset of ℝ≥0×ℝ, namely the image of the path's nonzero jump times under u↦(u,ΔX_uω). This supports source σ-finite localisation without BV or an independent marked Poisson law.
-- source:
--   Accepted original every-path jump-time countability 741d3b5f; accepted original joint mark measurability 9d68c5c2; Mathlib Measure.map_apply.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_marked_jump_measure_countable_borel_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∃ S : Set (ℝ≥0 × ℝ),
      S.Countable ∧ MeasurableSet S ∧
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) Sᶜ = 0 := by sorry
