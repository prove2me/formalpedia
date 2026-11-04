-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_mark_union_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_mark_union_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:05:40.477401+00:00
-- url     : https://prove2.me/theorems/3d111d88-78d5-450c-8e96-d65e5625cf5e
-- title:
--   Exact disjoint Borel mark splitting for the genuine original intrinsic Lévy jump count
-- statement:
--   The genuine original marked jump measure on a future rectangle has exact pathwise additivity over disjoint mark bands. This transfers the Borel semiring count structure without invoking ν-intensity, a Poisson copy or integrability.
-- source:
--   Source intrinsic marked count; Mathlib Set.prod_union and MeasureTheory.measure_union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_mark_union_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B C : Set ℝ) (hC : MeasurableSet C)
    (hBC : Disjoint B C) :
    ∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B ∪ C)) =
      ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) + ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ C) := by sorry
