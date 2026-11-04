-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_empty_time_window_mean_zero
-- name    : AvramDividend.Classical.avram_p2_d_future_original_empty_time_window_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:06:23.83707+00:00
-- url     : https://prove2.me/theorems/0c401781-5097-4ca5-a274-d55f85a1c5ed
-- title:
--   Original marked jump-count expectation vanishes on an empty half-open interval for every mark set
-- statement:
--   For the exact original spectrally negative Lévy path, positive nonzero source jump times, mapped marks, source measure P and any starting time s, the time interval (s,s] is empty, so the marked jump count and its lintegral vanish for every set of marks B. This handles the zero-length horizon even when the mark intensity is infinite.
-- source:
--   Set.Ioc_self and the original exact Measure.count.restrict/Measure.map marked count evaluated on a product with empty time factor; no compensation or ν intensity assumed.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_empty_time_window_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s s ×ˢ B) ∂P) = 0 := by sorry
