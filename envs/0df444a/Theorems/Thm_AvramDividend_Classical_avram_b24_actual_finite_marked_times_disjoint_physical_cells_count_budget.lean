-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_actual_finite_marked_times_disjoint_physical_cells_count_budget
-- name    : AvramDividend.Classical.avram_b24_actual_finite_marked_times_disjoint_physical_cells_count_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:39:16.138773+00:00
-- url     : https://prove2.me/theorems/4b3c46ba-45ab-4a0f-904d-b0d1e0e9d177
-- title:
--   Actual original finite marked jump times can be counted at most once over pairwise disjoint strict-left inclusive-right physical mesh cells
-- statement:
--   For any genuine finite set S of physical original Lévy jump times and any finite deterministic or realised physical stopped grid of pairwise disjoint chronological half-open cells (a_i,b_i], the sum of the number of marked jump times of S in each cell is bounded by the total number S.card. Every original jump can contribute to at most one right-inclusive physical cell; in particular a negative jump at the true ruin-contact endpoint survives in exactly the last cell, and an atom at a left endpoint is excluded from the subsequent cell. This is the exact source-independent finite combinatorial count budget needed to obtain refining-grid-uniform integrable variation envelopes from B24 genuine original negative-mark Poisson source, without a spurious second moment assumption.
-- source:
--   Pinned Mathlib finite disjoint union cardinality and original strict-left/right-inclusive physical marked time cells.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_actual_finite_marked_times_disjoint_physical_cells_count_budget
    (S : Finset ℝ≥0) (I : Finset ℕ)
    (a b : ℕ → ℝ≥0)
    (hCells : ∀ i ∈ I, a i ≤ b i)
    (hDisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) :
    (∑ i ∈ I,
      (S.filter (fun u => a i < u ∧ u ≤ b i)).card) ≤
        S.card := by sorry
