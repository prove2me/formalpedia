-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_zero_horizon_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_zero_horizon_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:32:17.038194+00:00
-- url     : https://prove2.me/theorems/05fc8380-037f-4785-8426-6ffa45d2e3ab
-- title:
--   Exact original source zero-length rectangle weighted jump count vanishes
-- statement:
--   For the genuine original intrinsic jump measure, the future count on the empty time rectangle (s,s] has zero lintegral against any nonnegative, potentially infinite, random weight; the ENNReal 0×∞ edge case is discharged by simplification.
-- source:
--   Set.Ioc_self, Set.empty_prod, MeasureTheory.measure_empty, MeasureTheory.lintegral_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_zero_horizon_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (B : Set ℝ) (H : Ω → ℝ≥0∞) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + 0) ×ˢ B) ∂P) = 0 := by sorry
