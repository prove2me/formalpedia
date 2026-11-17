-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_marked_support_monotone_halfopen_grid_disjoint_partition_20261116
-- name    : AvramDividend.Classical.avram_a27_finite_marked_support_monotone_halfopen_grid_disjoint_partition_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:11:46.473637+00:00
-- url     : https://prove2.me/theorems/f561fb40-048f-4038-a52d-f8792cedbdc0
-- title:
--   Finite marked-time support partitions into disjoint cells on any monotone half-open grid
-- statement:
--   Any finite original-time marked-jump support S contained in (u_0,u_n] of a monotone half-open time grid has exact partition into the finite subsets in consecutive grid cells, with pairwise disjoint cell subsets. Derive coverage from the already Proved exact Ioc finite-grid union lemma da209dde, and disjointness from monotonicity of u. This is the finite deterministic support partition needed for the original physical marked-count collision implication, without any probability-space changes.
-- source:
--   Proved monotone half-open exact grid interval partition da209dde plus Finset filter and disjointness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_finite_marked_support_monotone_halfopen_grid_disjoint_partition_20261116
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (S : Finset ℝ≥0)
    (hS : ∀ t ∈ S, t ∈ Ioc (u 0) (u n)) :
    let F : ℕ → Finset ℝ≥0 := fun i =>
      S.filter (fun t => t ∈ Ioc (u i) (u (i + 1)))
    (Finset.range n).biUnion F = S ∧
      ((Finset.range n : Set ℕ).PairwiseDisjoint F) := by sorry
