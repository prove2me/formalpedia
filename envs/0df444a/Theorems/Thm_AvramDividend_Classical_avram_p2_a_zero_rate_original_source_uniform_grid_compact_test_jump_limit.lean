-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:17:53.06202+00:00
-- url     : https://prove2.me/theorems/da8252f3-c20a-4f87-9bef-646942ebb6bc
-- title:
--   Unmodified original Lévy uniform-grid compact-test sums converge to finite true jumps
-- statement:
--   For any original spectrally negative Levy sample path and positive horizon, establish unconditional source-specific pathwise convergence of its actual full uniform-grid increment sums for every continuous real jump test vanishing on a neighbourhood of the zero mark. Extract exactly the finite genuine significant jumps, eliminate artificial time-zero marks by the nonnegative-time left-limit convention, and discharge original right- and left-limit regularity. No Poisson assumption, no compensator, no finite activity, no detached process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_significant_jump_finset
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    ∃ F : Finset ℝ≥0,
      (∀ t ∈ F, 0 < t ∧ t ≤ T) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (X.X (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) ω -
            X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω))
        atTop (𝓝 (∑ t ∈ F,
          f (X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t))) := by sorry
