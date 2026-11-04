-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:46:19.157011+00:00
-- url     : https://prove2.me/theorems/04532cfd-ad65-4e77-b288-b35c8af0cce2
-- title:
--   Source Lévy countable additivity over disjoint time and varying mark rectangles
-- statement:
--   The true original intrinsic Lévy marked jump count over a countable union of pairwise disjoint time intervals with potentially different Borel mark bands equals the extended-real sum of rectangle counts, path by path. No ν-rate or moment condition.
-- source:
--   SpectrallyNegativeLevy original intrinsic count.restrict.map, Mathlib measure_iUnion for pairwise disjoint Borel sets, product disjointness from separated time windows.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hTimeDisj : Pairwise (fun i j =>
      Disjoint (Ioc (s i) (t i)) (Ioc (s j) (t j))))
    (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, Ioc (s n) (t n) ×ˢ B n) =
    ∑' n, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s n) (t n) ×ˢ B n) := by sorry
