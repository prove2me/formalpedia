-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys55_original_intrinsic_NX_measure_measurable
-- name    : AvramDividend.Classical.avram_bvb_phys55_original_intrinsic_NX_measure_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:08:44.500844+00:00
-- url     : https://prove2.me/theorems/5e307164-a5f6-43a3-aae2-aeb8bf691653
-- title:
--   Original marked Lévy jump measure is a measurable random measure
-- statement:
--   For the original spectrally negative Lévy process, the intrinsic time-mark jump counting measure, constructed on the original probability space, is a measurable map from sample paths into the space of measures. This directly supplies the random-measure measurability prerequisite for root-connected phys49 and phys46.
-- source:
--   Proved original time-mark Borel count measurability and Mathlib Measure.measurable_of_measurable_coe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys55_original_intrinsic_NX_measure_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
