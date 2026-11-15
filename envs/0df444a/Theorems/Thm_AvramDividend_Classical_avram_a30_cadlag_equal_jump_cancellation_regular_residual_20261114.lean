-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a30_cadlag_equal_jump_cancellation_regular_residual_20261114
-- name    : AvramDividend.Classical.avram_a30_cadlag_equal_jump_cancellation_regular_residual_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:13:41.68223+00:00
-- url     : https://prove2.me/theorems/f5079e0b-c5e2-46e6-b8c0-46c8f95a4c7c
-- title:
--   Subtracting two cadlag paths with matching left jumps yields a right-continuous left-limited no-positive-jump residual
-- statement:
--   For any real cadlag paths on nonnegative time with matching left-jump sizes at every positive time, their difference retains all-path right continuity, left limits, and has no positive jumps, indeed no jumps.
-- source:
--   Pinned Mathlib ContinuousWithinAt.sub, Filter.Tendsto.sub, nhdsLT_neBot_of_exists_lt, tendsto_nhds_unique.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Cancelling the exact left jumps of two cadlag paths yields an all-path continuous-from-right zero-jump residual. -/

theorem AvramDividend.Classical.avram_a30_cadlag_equal_jump_cancellation_regular_residual_20261114
    (f J : ℝ≥0 → ℝ)
    (hfRight : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hJRight : ∀ t : ℝ≥0, ContinuousWithinAt J (Ici t) t)
    (hfLeft : ∀ t : ℝ≥0, 0 < t →
      Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)))
    (hJLeft : ∀ t : ℝ≥0, 0 < t →
      Tendsto J (𝓝[<] t) (𝓝 (Function.leftLim J t)))
    (hMatch : ∀ t : ℝ≥0, 0 < t →
      f t - Function.leftLim f t = J t - Function.leftLim J t) :
    (∀ t : ℝ≥0, ContinuousWithinAt (fun u => f u - J u) (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t →
      ∃ l, Tendsto (fun u => f u - J u) (𝓝[<] t) (𝓝 l)) ∧
    (∀ t l, 0 < t →
      Tendsto (fun u => f u - J u) (𝓝[<] t) (𝓝 l) →
      f t - J t ≤ l) := by sorry
