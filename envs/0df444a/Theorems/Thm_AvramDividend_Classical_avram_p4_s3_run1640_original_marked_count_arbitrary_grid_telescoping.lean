-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_marked_count_arbitrary_grid_telescoping
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_original_marked_count_arbitrary_grid_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:31:16.403005+00:00
-- url     : https://prove2.me/theorems/6fc70003-a1e4-4d6b-b91d-b90174ef4d57
-- title:
--   Exact original Lévy marked-jump counts telescope on any nondecreasing finite grid without zero-start assumption
-- statement:
--   For every actual original Lévy sample path and Borel mark B, a finite deterministic increasing grid may start at any nonnegative time. The sum of original physical jump counts across all n grid cells exactly equals the original marked count over the entire interval from grid zero to grid n, with no finite-count or stationarity assumption.
-- source:
--   Inductively apply the exact general original jump count partition on (grid0,gridk+1] and derive grid0≤gridk from its successor monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_intrinsic_marked_general_interval_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_original_marked_count_arbitrary_grid_telescoping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (B : Set ℝ) (hB : MeasurableSet B) (n : ℕ) :
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (I ×ˢ B)
    (∑ i ∈ Finset.range n, J (Ioc (grid i) (grid (i + 1)))) =
      J (Ioc (grid 0) (grid n)) := by sorry
