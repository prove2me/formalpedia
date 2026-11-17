-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_finite_marked_support_grid_mismatch_forces_double_source_cell_20261116
-- name    : AvramDividend.Classical.avram_a27_original_finite_marked_support_grid_mismatch_forces_double_source_cell_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:14:42.996634+00:00
-- url     : https://prove2.me/theorems/f679bbfc-fdbd-4ac6-acb6-327639fc6d15
-- title:
--   A miscount between original finite marked-time support and original physical occupied grid forces a double physical cell
-- statement:
--   For one actual original spectrally negative Lévy sample path, assume its exact B-marked jump-time set S on (0,T] is finite. On each positive equal-width half-open grid, if S.card differs from the count of cells containing a physical B-marked jump, then a physical cell must contain at least two B-marked jumps. Prove with the Proved finite original source cell count-cardinality identity 11e24cb0, finite disjoint marked support partition f561fb40, and finite partition miscount lemma 2f5b7419. This is pathwise and uses only original physical marked jumps, no independent source or probability law.
-- source:
--   Proved original finite physical cell source cardinality 11e24cb0, finite marked support grid partition f561fb40 and mismatch theorem 2f5b7419.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_finite_marked_support_grid_mismatch_forces_double_source_cell_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔
       0 < u ∧ u ≤ T ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B)
    (n : ℕ) (hn : 0 < n) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    S.card ≠ ((Finset.range n).filter (fun i : ℕ =>
      NX (Ioc ((i : ℝ≥0) * δ)
        (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) ≠ 0)).card →
    ∃ i ∈ Finset.range n,
      (2 : ℝ) ≤
        (NX (Ioc ((i : ℝ≥0) * δ)
          (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)).toReal := by sorry
