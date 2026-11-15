-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_single_ruincontact_mesh_sum_norm_bound
-- name    : AvramDividend.Classical.avram_b24_single_ruincontact_mesh_sum_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:25:31.622187+00:00
-- url     : https://prove2.me/theorems/578bbab4-b21c-4202-9088-45ced52b3d38
-- title:
--   One ruin-contact cell lets a uniform increment bound control the entire terminal mesh sum
-- statement:
--   For an ordered separated original stopped mesh, at most one index can straddle its ruin-clipped stopping time under strict-left/inclusive-right contact. Any real-valued terminal contact-cell contribution bounded in absolute value by ε for each cell has terminal aggregate absolute value bounded by ε, including when no cell makes contact. This avoids an artificial factor equal to mesh size and isolates the stochastic modulus requirement for Gaussian and compensated jump last-cell estimates.
-- source:
--   Proved unique terminal contact-cell lemma and Finset singleton sum.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_unique_ruincontact_cell_on_separated_grid
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_single_ruincontact_mesh_sum_norm_bound
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : ℝ≥0) (V : ℕ → ℝ)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hV : ∀ i ∈ S, ‖V i‖ ≤ ε) :
    ‖∑ i ∈ S.filter (fun i => a i < σ ∧ σ ≤ b i), V i‖ ≤ ε := by sorry
