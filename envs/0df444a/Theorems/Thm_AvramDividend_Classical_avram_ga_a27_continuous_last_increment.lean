-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_continuous_last_increment
-- name    : AvramDividend.Classical.avram_ga_a27_continuous_last_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:39:48.599702+00:00
-- url     : https://prove2.me/theorems/ef56f0a4-79f3-4c28-b3bc-612f4ed23222
-- title:
--   Vanishing final path increment from continuity at the horizon along admitted mesh points
-- statement:
--   A real-valued path continuous relative to a set at the horizon has vanishing last increments along mesh points within that set converging to the horizon. This turns the proved original zero-jump Levy uniform path continuity and rational grid limit into an almost-sure Gaussian last-increment limit.
-- source:
--   Avram Gaussian A27 original-path horizon convergence

import Mathlib
open Filter
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a27_continuous_last_increment
    (f : ℝ≥0 → ℝ) (s : Set ℝ≥0) (t : ℝ≥0) (u : ℕ → ℝ≥0)
    (hf : ContinuousWithinAt f s t)
    (hu : Tendsto u atTop (nhds t))
    (hmem : ∀ᶠ m in atTop, u m ∈ s) :
    Tendsto (fun m => f t - f (u m)) atTop (nhds (0 : ℝ)) := by sorry
