-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
-- name    : AvramDividend.Classical.avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:53:55.303975+00:00
-- url     : https://prove2.me/theorems/4036e0ab-7c6b-42f7-92fe-263697ef1e74
-- title:
--   Every finite set of original nonnegative jump times has a positive pairwise separation
-- statement:
--   The exact source marked-jump times have already been shown finite. For a finite set F of NNReal time points, there exists a strictly positive real gap smaller than or equal to every distance between distinct points of F. This purely geometric lemma is the input for the fine deterministic-grid proof for the actual original jump paths.
-- source:
--   Finite-set geometry for Avram W7-06 original jump-time grid occupation; no new sample space or stochastic process.

import Mathlib
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
    (F : Finset ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ F, ∀ v ∈ F, u ≠ v →
        δ ≤ |(u : ℝ) - (v : ℝ)| := by sorry
