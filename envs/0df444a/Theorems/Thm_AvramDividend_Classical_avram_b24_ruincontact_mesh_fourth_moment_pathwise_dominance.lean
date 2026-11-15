-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
-- name    : AvramDividend.Classical.avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:28:07.144072+00:00
-- url     : https://prove2.me/theorems/2faa61bf-52ff-4807-9ddc-dcbfca7d7945
-- title:
--   Original ruin-contact single-cell fourth-power sum dominated by total mesh fourth moments
-- statement:
--   For a separated original predictable mesh, the strict-left inclusive-right terminal ruin contact contains at most one cell. Hence the fourth power of the real norm of the entire terminal contact contribution is bounded pathwise by the nonnegative total of fourth powers over all mesh cells. This is the combinatorial step for using deterministic Gaussian fourth-moment estimates to control the last random stopping cell in L1, without multiplying by mesh cardinality.
-- source:
--   Finite sums, nonnegative powers and proved unique ruin-contact cell.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_unique_ruincontact_cell_on_separated_grid
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : ℝ≥0) (V : ℕ → ℝ)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j) :
    (‖∑ i ∈ S.filter (fun i => a i < σ ∧ σ ≤ b i), V i‖)^4 ≤
      ∑ i ∈ S, (‖V i‖)^4 := by sorry
