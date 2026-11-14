-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_compact_uniform_real_rates_to_locally_uniform_20261113
-- name    : AvramDividend.Classical.avram_a24_compact_uniform_real_rates_to_locally_uniform_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:52:22.031361+00:00
-- url     : https://prove2.me/theorems/d6551a09-0c59-4dbc-8e81-cd1a76ee5628
-- title:
--   Compact-uniform real error bounds imply local uniform convergence on every one-sided time half-line
-- statement:
--   A sequence of real functions on nonnegative times whose errors are uniformly small on every bounded horizon converges locally uniformly on the right-sided time set at each time.
-- source:
--   Pinned Mathlib Metric.tendstoLocallyUniformlyOn_iff, Archimedean natural bound and finite-horizon real error estimates.

import Mathlib
open Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

/-- Uniform real error bounds on every compact nonnegative horizon imply locally uniform convergence on each right half-line. -/

theorem AvramDividend.Classical.avram_a24_compact_uniform_real_rates_to_locally_uniform_20261113
    (F : ℕ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ)
    (hRate : ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ u : ℝ≥0, u ≤ (K : ℝ≥0) →
        |F n u - g u| ≤ ε) :
    ∀ t : ℝ≥0, TendstoLocallyUniformlyOn F g atTop (Ici t) := by sorry
