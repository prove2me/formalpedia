-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB92_same_grid_step_product_diagonal
-- name    : AvramDividend.Classical.avram_gbB92_same_grid_step_product_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:29:02.406372+00:00
-- url     : https://prove2.me/theorems/5ceed41c-3aa1-458f-9a04-e385ab0ea9a2
-- title:
--   Product of two same-grid indicator sums has only diagonal cells
-- statement:
--   Half-open cells of a uniform grid with positive width are pairwise disjoint. Thus at most one cell indicator is nonzero at any time, so multiplying two same-grid step sums leaves only their same-cell diagonal products.
-- source:
--   Algebraic same-grid product child of the two-grid pointwise refinement B84.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB92_same_grid_step_product_diagonal
    (N : ℕ) (δ t : ℝ) (hδ : 0 < δ)
    (H J : ℕ → ℝ) :
    ((Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then H r else 0)) *
    ((Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then J r else 0)) =
    (Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then H r * J r else 0) := by sorry
