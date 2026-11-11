-- Prove2me | solution 1 for levy_foundations_public_semigroup_scaled_largeSet_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:40:25.64096+00:00
-- url     : https://prove2.me/submissions/3bd5aead-be06-46ca-abce-79d2ce53b026

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_bound_of_exponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Semigroup exponent continuity at zero forces uniform decay of scaled
large-jump masses as the spatial cutoff tends to infinity. -/
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : {t : ℝ // 0 < t},
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet R)).toReal ≤ δ := by
  have hcont : Tendsto (fun ξ : ℝ => ‖S.exponent ξ‖)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun ξ : ℝ => ‖S.exponent ξ‖)
        (𝓝 (0 : ℝ)) (𝓝 ‖S.exponent 0‖) :=
      S.exponent_continuous.norm.continuousAt
    simpa only [S.exponent_zero, norm_zero] using hc
  have hsmallset : {ξ : ℝ | ‖S.exponent ξ‖ < δ / 4} ∈ 𝓝 (0 : ℝ) := by
    have hIio : Set.Iio (δ / 4) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by positivity)
    exact hcont.eventually hIio
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp hsmallset
  let R : ℝ := 2 / η + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hident : η * R = 2 + η := by
    dsimp [R]
    field_simp [ne_of_gt hη]
  have hfreq : 2 / R < η := by
    apply (div_lt_iff₀ hR).mpr
    rw [hident]
    linarith
  refine ⟨R, hR, ?_⟩
  intro t
  have hψ : ∀ ξ ∈ Set.Icc (0 : ℝ) (2 / R),
      ‖S.exponent ξ‖ ≤ δ / 4 := by
    intro ξ hξ
    have hdist : dist ξ (0 : ℝ) < η := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hξ.1]
      exact lt_of_le_of_lt hξ.2 hfreq
    have hξ_ball : ξ ∈ Metric.ball (0 : ℝ) η :=
      Metric.mem_ball.mpr hdist
    exact le_of_lt (hηball hξ_ball)
  calc
    t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet R)).toReal
        ≤ 4 * (δ / 4) :=
          levy_foundations_public_semigroup_scaled_largeSet_bound_of_exponent
            S R hR (δ / 4) hψ t
    _ = δ := by ring
