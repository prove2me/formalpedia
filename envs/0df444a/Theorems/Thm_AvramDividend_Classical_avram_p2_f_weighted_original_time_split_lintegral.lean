-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_time_split_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_time_split_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:42:13.548308+00:00
-- url     : https://prove2.me/theorems/dfef2850-0a0d-4d9b-99e9-d368ed2953b7
-- title:
--   Weighted original Lévy expected marked jump-count additivity across adjacent time windows
-- statement:
--   For the genuine original Lévy intrinsic marked jump measure, any nonnegative measurable path weight times the source count over a pair of adjacent half-open future intervals integrates to the sum of weighted counts for each interval. Valid for infinite weights/counts and does not identify ν.
-- source:
--   Source intrinsic pathwise time-split additivity, intrinsic rectangle measurability, Mathlib lintegral_add_left and ENNReal.mul_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_time_split_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s a b : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s (s + (a + b)) ×ˢ B) ∂P) =
    (∫⁻ ω, H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s (s + a) ×ˢ B) ∂P) +
    (∫⁻ ω, H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc (s + a) ((s + a) + b) ×ˢ B) ∂P) := by sorry
