-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_real_grid_compact_test_pathwise_exists
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_real_grid_compact_test_pathwise_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:45:55.754203+00:00
-- url     : https://prove2.me/theorems/dd0e830a-81eb-4988-8ec6-a219796fc0a3
-- title:
--   Genuine original Lévy real-grid compact-test paths converge at every sample
-- statement:
--   Show the exact almost-everywhere-existence premise needed by the independently Proved P2-J original Lévy compact negative expectation convergence theorem. For every original source sample, the true-jump finite-sum limit exists by P2-A full source-grid convergence; the actual grid matches the P2-J real-to-NNReal step through a pinned arithmetic identity. The pathwise result holds for all samples, without assuming a jump compensator, or an analytic Lévy-rate law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_real_grid_compact_test_pathwise_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    ∀ ω : Ω, ∃ z : ℝ,
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (X.X (((i + 1 : ℕ) : ℝ≥0) *
              Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
            X.X ((i : ℝ≥0) *
              Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
        atTop (𝓝 z) := by sorry
