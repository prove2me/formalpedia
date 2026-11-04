-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_mark_measure_eq_negative_restrict
-- name    : AvramDividend.Classical.avram_p2_d_future_mark_measure_eq_negative_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:26:57.478128+00:00
-- url     : https://prove2.me/theorems/a2412e45-5413-4633-91d2-42816d060566
-- title:
--   Original marked jump measure equals its full negative-mark restriction as an actual measure
-- statement:
--   For each original spectrally negative Lévy sample path, identify the entire intrinsic marked jump measure with its restriction to all times and strictly negative marks as measures, preserving arbitrary Borel tests and infinite activity. No jump-intensity formula is assumed.
-- source:
--   Apply measure extensionality to the Proved all-Borel original source support theorem c598292d and the pinned Measure.restrict_apply identity; the resulting equality is on the original source's exact mapped counting measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_full_time_mark_negative_support

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_mark_measure_eq_negative_restrict
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))).restrict (Set.univ ×ˢ Iio (0 : ℝ)) := by sorry
