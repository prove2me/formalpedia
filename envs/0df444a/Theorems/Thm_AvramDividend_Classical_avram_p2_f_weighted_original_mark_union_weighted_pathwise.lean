-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_mark_union_weighted_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_mark_union_weighted_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:07:53.139708+00:00
-- url     : https://prove2.me/theorems/76c568a2-e16f-4621-ade9-c946ed55e4f4
-- title:
--   Exact original-source disjoint mark partition with arbitrary nonnegative random weight
-- statement:
--   Pathwise exact mark-additivity remains valid after multiplication by arbitrary nonnegative ENNReal weight, including infinite values and without any adaptedness or rate assumption. Uses true original jumps.
-- source:
--   Original source jump measure and MeasureTheory.measure_union with ENNReal mul_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_mark_union_weighted_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B C : Set ℝ) (hC : MeasurableSet C)
    (hBC : Disjoint B C) (H : Ω → ℝ≥0∞) :
    ∀ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B ∪ C)) =
      H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) + H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ C) := by sorry
