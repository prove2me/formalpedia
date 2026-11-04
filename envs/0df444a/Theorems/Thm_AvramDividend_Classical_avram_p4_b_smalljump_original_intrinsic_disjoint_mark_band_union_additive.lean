-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:02:54.780498+00:00
-- url     : https://prove2.me/theorems/5e8d380a-c740-475e-96ec-5529d0580646
-- title:
--   Original intrinsic Levy jump counts add over disjoint Borel mark bands
-- statement:
--   For the original source marked jump count of SpectrallyNegativeLevy, the number of physical jumps in a time rectangle and a disjoint Borel union of mark sets equals the sum over the two mark sets pathwise.
-- source:
--   Exact original intrinsic marked measure and measure additivity over disjoint measurable product rectangles.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (B ∪ C)) =
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) +
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ C) := by sorry
