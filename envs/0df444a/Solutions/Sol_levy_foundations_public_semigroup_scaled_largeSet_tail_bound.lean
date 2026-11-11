-- Prove2me | solution 1 for levy_foundations_public_semigroup_scaled_largeSet_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:27:26.887112+00:00
-- url     : https://prove2.me/submissions/c73e622c-1b05-4d67-903b-db2c87143917

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_quantitative_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution (S : ProbabilityTheory.ConvolutionSemigroup) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : {t : ℝ // 0 < t},
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet R)).toReal ≤ ε := by
  have hξ_exist : ∃ r : ℝ, 0 < r ∧ ∀ ξ, |ξ| < r → ‖S.exponent ξ‖ < ε/4 := by
    have htend : Tendsto (fun ξ : ℝ => ‖S.exponent ξ‖) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto S.exponent (𝓝 0) (𝓝 0) := by
        have := S.exponent_continuous.tendsto 0
        rw [S.exponent_zero] at this
        exact this
      have h2 : Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) := by
        have := (continuous_norm (E := ℂ)).tendsto 0
        simpa using this
      exact h2.comp h1
    have hnhds : ∀ᶠ ξ in 𝓝 (0 : ℝ), ‖S.exponent ξ‖ < ε/4 :=
      htend.eventually (Iio_mem_nhds (by linarith))
    rw [Metric.eventually_nhds_iff] at hnhds
    obtain ⟨r, hr_pos, hr⟩ := hnhds
    exact ⟨r, hr_pos, fun ξ hξ => hr (by simpa [Real.dist_eq, sub_zero] using hξ)⟩
  obtain ⟨r, hr_pos, hr⟩ := hξ_exist
  set R := max (1 : ℝ) (2 / r + 1) with hR_def
  have hR_ge_one : 1 ≤ R := le_max_left _ _
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos hR_ge_one
  have hR_inv : 2 / R < r := by
    have h_denom_pos : (0 : ℝ) < 2 / r + 1 := by positivity
    have h1 : 2 / R ≤ 2 / (2 / r + 1) :=
      div_le_div_of_nonneg_left (by norm_num) h_denom_pos (le_max_right _ _)
    have h2 : 2 / (2 / r + 1) < r := by
      rw [div_lt_iff₀ h_denom_pos]
      have h3 : (2 / r + 1) * r = 2 + r := by field_simp
      linarith [h3]
    linarith
  have hM_bound : ∀ ξ ∈ Set.Icc (0:ℝ) (2/R), ‖S.exponent ξ‖ ≤ ε/4 := by
    intro ξ hξ
    have h1 : |ξ| < r := by
      rw [abs_of_nonneg hξ.1]
      exact lt_of_le_of_lt hξ.2 hR_inv
    exact le_of_lt (hr ξ h1)
  refine ⟨R, hR_ge_one, fun t => ?_⟩
  calc t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet R)).toReal
      ≤ 4 * (ε/4) := levy_foundations_public_semigroup_scaled_largeSet_quantitative_bound S R hR_pos (ε/4) hM_bound t
    _ = ε := by ring
