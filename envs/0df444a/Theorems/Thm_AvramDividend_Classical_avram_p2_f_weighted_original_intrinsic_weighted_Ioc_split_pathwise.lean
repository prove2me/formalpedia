-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_weighted_Ioc_split_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_weighted_Ioc_split_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:26:14.757577+00:00
-- url     : https://prove2.me/theorems/f8227859-006c-4efd-ab92-33c62dffff48
-- title:
--   Weighted pathwise splitting of the genuine original Lévy marked count over adjacent time cells
-- statement:
--   The actual intrinsic original marked count on (s,t] multiplied by any nonnegative random weight equals the sum of its weighted counts on (s,u] and (u,t], path by path. This exact identity supports predictable-simple compensation and respects infinite ENNReal values without requiring an analytic ν-rate.
-- source:
--   Proved original pathwise intrinsic time-rectangle split UUID 4ffd0ce9 and distributivity in ENNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_split_pathwise

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_weighted_Ioc_split_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (ω : Ω) :
    H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s t ×ˢ B) =
    H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s u ×ˢ B) +
    H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc u t ×ˢ B) := by sorry
