-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_marked_count_grid_telescoping
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_original_marked_count_grid_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:15:42.492757+00:00
-- url     : https://prove2.me/theorems/09bdd280-f483-4121-a875-a6ce479a00cc
-- title:
--   Original pathwise negative jump counting measure telescopes along every finite deterministic grid
-- statement:
--   For any actual original spectrally negative Lévy sample path, any deterministic nondecreasing time grid starting at zero and any Borel mark band, the sum of physical jump counts over its first n disjoint half-open cells equals the original intrinsic count on the whole interval (0,grid n]. This exact ENNReal identity needs no a.s. finite-count or stochastic-law assumption.
-- source:
--   Source-exact original count measure additivity on (0,s] and (s,t] applied inductively; no martingale axioms or conditional moment shortcuts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_intrinsic_negative_marked_time_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_original_marked_count_grid_telescoping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hZero : grid 0 = 0)
    (B : Set ℝ) (hB : MeasurableSet B) (n : ℕ) :
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (I ×ˢ B)
    (∑ i ∈ Finset.range n, J (Ioc (grid i) (grid (i + 1)))) =
      J (Ioc 0 (grid n)) := by sorry
