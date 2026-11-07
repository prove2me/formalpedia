-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_diagonal_refinement
-- name    : AvramDividend.Classical.avram_bv_strict6_diagonal_refinement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:28:57.909559+00:00
-- url     : https://prove2.me/theorems/9452c62b-39c0-4ca8-9c1a-e59b31625390
-- title:
--   Diagonal refinement selecting vanishing source errors across original BV compact bands
-- statement:
--   When each fixed compact-band error tends to zero with physical-mesh refinement, choose for every band k a mesh index at least k whose absolute error is strictly below 1/(k+1). This is the independent diagonal selection step needed when matching the original stopped BV C1 Taylor mesh with the growing bands of the proved original compensated-jump source. It does not assert that the physical source errors vanish; that substantive source convergence remains a separate obligation.

import Mathlib
open Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_diagonal_refinement
    (E : ℕ → ℕ → ℝ)
    (hvanish : ∀ k, Tendsto (fun n => E k n) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ,
      (∀ k, k ≤ φ k) ∧
      (∀ k, |E k (φ k)| < 1 / ((k : ℝ) + 1)) := by sorry
