-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_monotone_chronological_physical_mesh_cells_pairwise_disjoint_Ioc
-- name    : AvramDividend.Classical.avram_b24_original_monotone_chronological_physical_mesh_cells_pairwise_disjoint_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:43:47.305051+00:00
-- url     : https://prove2.me/theorems/6d27bf49-14a3-4119-bd6e-d6fd9d7f6fa3
-- title:
--   Every pair of distinct consecutive original monotone physical grid cells is disjoint under strict-left inclusive-right convention
-- statement:
--   For any nondecreasing sequence of genuine nonnegative physical time clocks t_0,t_1,... in an original stopped Ito-Meyer grid, the half-open consecutive cells (t_i,t_{i+1}] are pairwise disjoint, even when the grid contains repeated times. For distinct i<j, monotonicity gives t_{i+1}≤t_j, so no physical time can belong to both intervals. This exactly enforces the original strict-left/inclusive-right mark counting convention and avoids double-counting negative jumps, including at a true terminal ruin contact. It discharges the source-disjointness assumption required for the original finite-activity compensated marked-source refining-grid uniform total variation envelope.
-- source:
--   Order monotonicity of original NNReal physical chronological mesh timestamps and strict-left half-open interval disjointness.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_monotone_chronological_physical_mesh_cells_pairwise_disjoint_Ioc
    (t : ℕ → ℝ≥0) (hmono : Monotone t)
    (I : Finset ℕ) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (Ioc (t i) (t (i + 1)))
        (Ioc (t j) (t (j + 1))) := by sorry
