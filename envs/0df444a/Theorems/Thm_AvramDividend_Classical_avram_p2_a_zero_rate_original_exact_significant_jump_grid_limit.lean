-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_exact_significant_jump_grid_limit
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_exact_significant_jump_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:18:56.314373+00:00
-- url     : https://prove2.me/theorems/464e3ed4-6d6a-4788-b186-39a546b02c7c
-- title:
--   Exact original Lévy uniform-grid compact-test limit with the genuine finite significant-jump selector
-- statement:
--   For the actual original Lévy sample path, all uniform-grid compact tests vanishing near zero converge to the finite sum over precisely the jumps of size at least rho in (0,T]. The selector has an iff membership statement, including the t=0 exclusion justified from the original half-line left-limit identity. No stochastic intensity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_significant_jump_finset
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_exact_significant_jump_grid_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    ∃ F : Finset ℝ≥0,
      (∀ t : ℝ≥0, t ∈ F ↔ 0 < t ∧ t ≤ T ∧
        ρ ≤ |X.X t ω -
          Function.leftLim (fun u : ℝ≥0 => X.X u ω) t|) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (X.X (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) ω -
            X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω))
        atTop (𝓝 (∑ t ∈ F,
          f (X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t))) := by sorry
