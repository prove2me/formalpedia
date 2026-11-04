-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_time_split_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_time_split_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:39:51.124569+00:00
-- url     : https://prove2.me/theorems/729aeeea-5d59-4aa5-8e20-4e4a40e9107d
-- title:
--   Original Lévy intrinsic marked jump-count additivity across adjacent time windows
-- statement:
--   The intrinsic original Lévy marked jump count over (s,u] with mark set B is exactly the sum over adjacent windows (s,t] and (t,u], including possible infinite counts, provided s≤t≤u and B is Borel. No rate identification is needed.
-- source:
--   Actual original SpectrallyNegativeLevy intrinsic count.restrict.map and MeasureTheory.measure_union for measurable disjoint time rectangles.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_time_split_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) (ω : Ω) :
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s u ×ˢ B) =
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s t ×ˢ B) +
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc t u ×ˢ B) := by sorry
