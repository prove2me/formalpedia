-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_diagonal_nonnegative_error_mean
-- name    : AvramDividend.Classical.avram_bv_strict6_diagonal_nonnegative_error_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:46:28.483168+00:00
-- url     : https://prove2.me/theorems/73296e53-555e-4b89-9f88-7280aaebdeb4
-- title:
--   Nonnegative original source expected errors admit a deterministic vanishing diagonal
-- statement:
--   For a family E(k,n) of nonnegative expected physical source errors, suppose each fixed spatial compact-band k has mean error tending to zero as the physical mesh n refines. The proved BV-STRICT6 diagonal selector gives mesh indices at least k whose selected means are bounded by 1/(k+1); the pinned Mathlib reciprocal limit and order squeeze prove those selected means tend to zero. This is a conditional reduction tool for the genuine original Lévy/Stieltjes source error, not a claim that the physical error hypothesis already holds.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_diagonal_refinement
open Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_diagonal_nonnegative_error_mean
    (E : ℕ → ℕ → ℝ)
    (hnonneg : ∀ k n, 0 ≤ E k n)
    (hvanish : ∀ k, Tendsto (fun n => E k n) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ,
      (∀ k, k ≤ φ k) ∧
      Tendsto (fun k => E k (φ k)) atTop (𝓝 0) := by sorry
