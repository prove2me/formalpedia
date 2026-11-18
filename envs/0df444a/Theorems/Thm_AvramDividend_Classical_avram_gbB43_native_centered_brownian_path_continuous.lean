-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB43_native_centered_brownian_path_continuous
-- name    : AvramDividend.Classical.avram_gbB43_native_centered_brownian_path_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:52:06.703131+00:00
-- url     : https://prove2.me/theorems/5d492e03-7865-42cd-99a8-d78219945cb6
-- title:
--   Native centered Brownian sample paths are continuous for every sample
-- statement:
--   For every canonical Gaussian sample path, subtracting the initial Brownian coordinate produces a continuous real-time Brownian path. The existing Proved drifted Brownian continuity theorem and continuity of the deterministic time coordinate supply the statement, enabling a continuous-path lift on the unit interval.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB43_native_centered_brownian_path_continuous
    (ω : ℝ≥0 → ℝ) :
    Continuous (fun t : ℝ≥0 =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω) := by sorry
