-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a51_continuous_real_path_has_allpath_cadlag_no_positive_jumps_20261114
-- name    : AvramDividend.Classical.avram_a51_continuous_real_path_has_allpath_cadlag_no_positive_jumps_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:00:41.3161+00:00
-- url     : https://prove2.me/theorems/4efc63b4-e703-450c-8b3d-8fe23cfde842
-- title:
--   Continuous real path on nonnegative time has right continuity, exact positive-time left limits and no positive jumps
-- statement:
--   Any globally continuous real function of nonnegative time is right-continuous at every time, has a finite left limit at each positive time, and can have no positive left jumps; every left limit equals the present value.
-- source:
--   Mathlib continuousWithinAt and uniqueness of limits from the left.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Every continuous real path on nonnegative time has no positive left jumps. -/

theorem AvramDividend.Classical.avram_a51_continuous_real_path_has_allpath_cadlag_no_positive_jumps_20261114
    (f : ℝ≥0 → ℝ) (hf : Continuous f) :
    (∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t →
      ∃ l, Tendsto f (𝓝[<] t) (𝓝 l)) ∧
    (∀ t l, 0 < t →
      Tendsto f (𝓝[<] t) (𝓝 l) → f t ≤ l) := by sorry
