-- Prove2me | solution 1 for leanlevy_chat33_scaled_small_ball_compensated_direct_identity_8738322f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:50:16.097013+00:00
-- url     : https://prove2.me/submissions/6a2f3541-9ed0-4bb7-87d7-a7198140c5a9

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_scaled_smallBall_remainder_tendsto
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_integrableOn_ball
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_sq_integrableOn_ball
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real
theorem solution (S : ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}} {σ_sq_r : ℝ}
    (hσ : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) atTop (𝓝 σ_sq_r))
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) 
    (hσ_bdd : ∃ C : ℝ, ∀ k, (t_seq k).val⁻¹ *
      ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) ≤ C)
    (hquad : Tendsto (fun k => (↑ξ ^ 2 / 2 : ℂ) *
      (↑((t_seq k).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2
        ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ))
      atTop (𝓝 ((↑ξ ^ 2 / 2 : ℂ) * (↑σ_sq_r : ℂ))))
    : ∀ k, ((t_seq k).val⁻¹ : ℂ) *
      ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
        ∂(S.measure (t_seq k) : Measure ℝ) =
      (((t_seq k).val⁻¹ : ℂ) * ∫ x in {x | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ)) -
      (↑ξ ^ 2 / 2 : ℂ) * (↑((t_seq k).val⁻¹ *
          ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ) := by
    have hrem := ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_scaled_smallBall_remainder_tendsto S hr hr1 ξ hν hν_r hσ_bdd h_jump
    intro k
    set μk : Measure ℝ := (S.measure (t_seq k) : Measure ℝ) with hμk_def
    have hmeas : MeasurableSet {x : ℝ | |x| < r} :=
      (isOpen_lt continuous_abs continuous_const).measurableSet
    have hRint : IntegrableOn
        (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
          + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) {x : ℝ | |x| < r} μk :=
      leanlevy_chat32_remainder_integrableOn_ball (le_of_lt hr) hr1 ξ μk
    have hQint : IntegrableOn (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) {x : ℝ | |x| < r} μk := by
      have hrw : (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) =
          fun x : ℝ => (↑((x ^ 2 * (ξ ^ 2 / 2) : ℝ)) : ℂ) := by
        funext x; push_cast; ring
      rw [hrw]
      exact (((leanlevy_chat32_sq_integrableOn_ball r μk).mul_const (ξ ^ 2 / 2))).ofReal
    have hsub : ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂μk =
        (∫ x in {x | |x| < r},
            (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂μk) -
          ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 ∂μk := by
      rw [← integral_sub hRint hQint]
      refine setIntegral_congr_fun hmeas (fun x _ => ?_)
      ring
    have hquad_real : ∫ x in {x | |x| < r}, (ξ ^ 2 / 2 * x ^ 2 : ℝ) ∂μk =
        ξ ^ 2 / 2 * ∫ x in {x | |x| < r}, x ^ 2 ∂μk :=
      integral_const_mul (ξ ^ 2 / 2) _
    have hquad_int : ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 ∂μk =
        (↑ξ ^ 2 / 2 : ℂ) * (↑(∫ x in {x | |x| < r}, x ^ 2 ∂μk) : ℂ) := by
      have hcongr : ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 ∂μk =
          ∫ x in {x | |x| < r}, (↑((ξ ^ 2 / 2 * x ^ 2 : ℝ)) : ℂ) ∂μk := by
        refine setIntegral_congr_fun hmeas (fun x _ => ?_)
        push_cast; ring
      rw [hcongr]
      rw [show (∫ x in {x | |x| < r}, (↑((ξ ^ 2 / 2 * x ^ 2 : ℝ)) : ℂ) ∂μk) =
          (↑(∫ x in {x | |x| < r}, (ξ ^ 2 / 2 * x ^ 2 : ℝ) ∂μk) : ℂ) from integral_ofReal]
      rw [hquad_real]
      push_cast
      ring
    rw [hsub, hquad_int, mul_sub]
    rw [hμk_def]
    push_cast
    ring
