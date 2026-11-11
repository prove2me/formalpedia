-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18h_uniform_cutoff_rate_rightcont_limit
-- name    : AvramDividend.Classical.avram_ja18h_uniform_cutoff_rate_rightcont_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:23:44.008961+00:00
-- url     : https://prove2.me/theorems/1f70835c-3dc7-49bb-a62e-1c505cbcfa18
-- title:
--   Uniform Cauchy modulus on compact time intervals preserves right-continuity of marked paths
-- statement:
--   Pure deterministic analysis: given right-continuous real-valued paths f_n on NNReal, common initial zero, and on every compact horizon a finite C/(n+1) uniform Cauchy modulus for n≤m, construct their pointwise limit g. Prove convergence for all times, g right-continuous at all times and g(0)=0. Does not use a stochastic identification, change the original probability space, or assume integrability of large marks.
-- source:
--   Generic analytic child for original same-omega path-only 9362895e; combine with Proved original count and quantitative modulus 99422ce0.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18h_uniform_cutoff_rate_rightcont_limit
    (f : ℕ → ℝ≥0 → ℝ)
    (hRight : ∀ (n : ℕ) (t : ℝ≥0),
      ContinuousWithinAt (f n) (Ici t) t)
    (hZero : ∀ n : ℕ, f n 0 = 0)
    (hRate : ∀ T : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0), t ≤ T →
        |f m t - f n t| ≤ (1 / ((n : ℝ) + 1)) * C) :
    ∃ g : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        Tendsto (fun n : ℕ => f n t) atTop (𝓝 (g t))) ∧
      (∀ t : ℝ≥0, ContinuousWithinAt g (Ici t) t) ∧
      g 0 = 0 := by sorry
