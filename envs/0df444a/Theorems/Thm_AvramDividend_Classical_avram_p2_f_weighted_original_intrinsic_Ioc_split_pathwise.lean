-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_split_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_Ioc_split_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:19:47.96945+00:00
-- url     : https://prove2.me/theorems/4ffd0ce9-55eb-4a6f-937d-b57462dd3571
-- title:
--   Actual intrinsic original marked jump measure is pathwise additive across adjacent time rectangles
-- statement:
--   For every sample path of the original Lévy process, its genuine intrinsic jump measure on (s,t] with Borel marks B equals the sum over adjacent intervals (s,u] and (u,t]. This exact count transport is independent of the Lévy ν-rate, stochastic independence and any Poisson replacement.
-- source:
--   MeasureTheory measure_union on disjoint adjacent half-open clock rectangles; original count.restrict and map definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_Ioc_split_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (ω : Ω) :
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s t ×ˢ B) =
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s u ×ˢ B) +
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc u t ×ˢ B) := by sorry
