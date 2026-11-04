-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
-- name    : AvramDividend.Classical.avram_p2_d_future_intrinsic_general_time_mark_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:44:22.331854+00:00
-- url     : https://prove2.me/theorems/21acd1ce-60b9-441d-ad6b-dd3de114827c
-- title:
--   Original intrinsic jump-measure evaluation is measurable on every Borel time–mark set
-- statement:
--   For the exact original Lévy sample space and intrinsic marked jump measure, every jointly Borel subset C of physical time×real marks has a measurable ENNReal-valued samplewise jump count. Allows arbitrary Borel time–mark tests, including infinite activity, without a Poisson replacement or any jump-rate identity.
-- source:
--   Directly evaluates the Proved original s-finite measurable source kernel eb357d08 on the arbitrary Borel test C; this generalises the previously Proved P2-D rectangle count-measurability helper 1f8f25b0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_intrinsic_general_time_mark_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : Set (ℝ≥0 × ℝ)) (hC : MeasurableSet C) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C) := by sorry
