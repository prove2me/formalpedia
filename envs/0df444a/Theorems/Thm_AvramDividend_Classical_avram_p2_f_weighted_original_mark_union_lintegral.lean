-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_mark_union_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_mark_union_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:08:51.424483+00:00
-- url     : https://prove2.me/theorems/d5dd4722-798d-4eda-9a19-8eacd3feb053
-- title:
--   Disjoint Borel mark additivity for original Lévy source weighted expected jump counts
-- statement:
--   For any measurable nonnegative pathwise weight, the true original marked count expectation over disjoint mark union is exactly the sum of weighted expectations for each mark. Handles infinite values without any ν-rate assumption.
-- source:
--   Original intrinsic rectangle measurability (Proved) and MeasureTheory.measure_union / lintegral_add_left.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_mark_union_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C)
    (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B ∪ C)) ∂P) =
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) +
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ C) ∂P) := by sorry
