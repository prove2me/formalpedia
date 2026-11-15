-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_unique_ruincontact_cell_on_separated_grid
-- name    : AvramDividend.Classical.avram_b24_unique_ruincontact_cell_on_separated_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:44:45.424124+00:00
-- url     : https://prove2.me/theorems/7cd7e55a-d9da-4450-b8e4-94f887ef8d76
-- title:
--   At most one ruin-contact cell in an ordered disjoint stopped physical mesh
-- statement:
--   For an ordered, disjoint real-time mesh, a fixed stopping time has at most one terminal contact cell whose left endpoint is strictly before the stopping time and whose right endpoint meets or exceeds it. This pathwise uniqueness is the combinatorial lemma needed for the true ruin-terminal cell; no post-ruin continuation or noise assumptions.
-- source:
--   Finite disjoint stopping grids, strict-left inclusive-right endpoint convention matching the ruin-clipped physical mesh.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_unique_ruincontact_cell_on_separated_grid
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (σ : ℝ≥0) :
    ∀ i ∈ S, ∀ j ∈ S,
      a i < σ → σ ≤ b i → a j < σ → σ ≤ b j → i = j := by sorry
