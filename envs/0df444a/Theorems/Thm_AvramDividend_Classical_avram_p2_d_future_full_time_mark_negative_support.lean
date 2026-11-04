-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_full_time_mark_negative_support
-- name    : AvramDividend.Classical.avram_p2_d_future_full_time_mark_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:06:29.37494+00:00
-- url     : https://prove2.me/theorems/c598292d-49e9-422a-8511-3c2f2fa4c638
-- title:
--   Original intrinsic jump measure is concentrated on negative marks for arbitrary jointly Borel time–mark sets
-- statement:
--   For the actual original spectrally negative Lévy sample path, the intrinsic marked count measure of any jointly Borel physical time–mark test C is exactly its restriction to strictly negative marks. This handles arbitrary time–mark regions, not merely Borel rectangles, and allows infinite sample counts.
-- source:
--   Combine Proved original joint Borel measurability of the jump mark 9d68c5c2 with Proved pointwise source jumpmark nonpositivity e95fe5bc, the nonzero-jump restriction, and pinned Mathlib Measure.map_apply/restrict_apply. On the support of the restricted count measure the mapped mark is strictly negative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_full_time_mark_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (C : Set (ℝ≥0 × ℝ)) (hC : MeasurableSet C) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (C ∩ (Set.univ ×ˢ Iio (0 : ℝ))) := by sorry
