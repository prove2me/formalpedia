-- Prove2me | solution 1 for levy_foundations_public_semigroup_scaled_small_sine_error_eventually_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:31:51.910493+00:00
-- url     : https://prove2.me/submissions/f023281b-7bb1-4ad9-84cf-414f6dd6d538

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_second_moment_eventually_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Bounded small-ball second moments are integrable under finite measures. -/
private lemma levy_foundations_aux_integrableOn_sq_smallSet
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IntegrableOn (fun x => x ^ 2) smallSet μ := by
  have hsmallMeas : MeasurableSet smallSet :=
    (isOpen_Iio.preimage continuous_abs).measurableSet
  refine IntegrableOn.of_bound (measure_lt_top _ _) ?_ 1 ?_
  · exact ((continuous_pow 2).measurable.aemeasurable.aestronglyMeasurable).restrict
  · exact (ae_restrict_mem hsmallMeas).mono (fun x hx => by
      have hxlt : |x| < 1 := (show x ∈ smallSet ↔ |x| < 1 from Iff.rfl).mp hx
      simp only [Real.norm_eq_abs]
      have h2 : x ^ 2 < 1 := by
        have h3 : |x| ^ 2 < 1 := pow_lt_one₀ (abs_nonneg x) hxlt two_ne_zero
        rwa [sq_abs] at h3
      rw [abs_of_nonneg (sq_nonneg x)]
      linarith)


/-- On the unit interval, the sine deviation is controlled by the quadratic term. -/
private lemma levy_foundations_aux_abs_sub_sin_le_sq_div_two {x : ℝ} (hx : |x| ≤ 1) :
    |x - Real.sin x| ≤ x ^ 2 / 2 := by
  by_cases hx0 : 0 ≤ x
  · -- x ≥ 0: x - sin x ≥ 0
    have hx1 : x ≤ 1 := (abs_of_nonneg hx0 ▸ hx)
    rcases eq_or_lt_of_le hx0 with rfl | hx_pos
    · simp
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.sin_le hx0))]
      nlinarith [Real.sin_gt_sub_cube hx_pos,
        mul_nonneg (show (0 : ℝ) ≤ 3 - x by linarith) (sq_nonneg x)]
  · -- x < 0: use sin(-x) = -sin x and (-x) ∈ (0, 1]
    push Not at hx0
    have hmx_pos : 0 < -x := neg_pos.mpr hx0
    have hmx1 : -x ≤ 1 := by linarith [show |x| = -x from abs_of_neg hx0]
    rw [show x - Real.sin x = -((-x) - Real.sin (-x)) from by simp [Real.sin_neg]; ring,
        abs_neg,
        abs_of_nonneg (sub_nonneg.mpr (Real.sin_le (le_of_lt hmx_pos)))]
    nlinarith [Real.sin_gt_sub_cube hmx_pos, sq_nonneg x,
      mul_nonneg (show (0 : ℝ) ≤ 3 - (-x) by linarith) (sq_nonneg (-x))]

/-- A quadratic sine remainder is uniformly bounded by the scaled small-ball moment. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      |(t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, (x - Real.sin x)
        ∂(S.measure (t_seq n) : Measure ℝ)| ≤ C := by
  have hmeas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hsubset : {x : ℝ | |x| < r} ⊆ smallSet :=
    fun x hx => (show x ∈ smallSet ↔ |x| < 1 from Iff.rfl).mpr
      (lt_of_lt_of_le hx hr1)
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    levy_foundations_public_semigroup_second_moment_eventually_bounded S ht
  refine ⟨C₂, ?_⟩
  filter_upwards [hC₂] with n hC₂n
  haveI hμ_prob : IsProbabilityMeasure (S.measure (t_seq n) : Measure ℝ) :=
    (S.measure (t_seq n)).prop
  have t_pos := (t_seq n).prop
  have hint_sin : Integrable (fun x => Real.sin x) (S.measure (t_seq n) : Measure ℝ) :=
    Integrable.of_bound Real.continuous_sin.aestronglyMeasurable 1
      (ae_of_all _ fun x => by simp [abs_le.mpr ⟨Real.neg_one_le_sin x,
        Real.sin_le_one x⟩])
  have hint_x_small : IntegrableOn (fun x => x) {x | |x| < r}
      (S.measure (t_seq n) : Measure ℝ) :=
    IntegrableOn.of_bound (measure_lt_top _ _)
      continuous_id.aestronglyMeasurable.restrict 1
      ((ae_restrict_mem hmeas_ball).mono
        (fun x hx => by
          simp only [Real.norm_eq_abs]
          exact (lt_of_lt_of_le hx hr1).le))
  have hint_sin_small : IntegrableOn (fun x => Real.sin x) {x | |x| < r}
      (S.measure (t_seq n) : Measure ℝ) :=
    hint_sin.integrableOn
  have hint_xsin_small : IntegrableOn (fun x => x - Real.sin x) {x | |x| < r}
      (S.measure (t_seq n) : Measure ℝ) :=
    (hint_x_small.sub hint_sin_small)
  have hint_sq_small : IntegrableOn (fun x => x ^ 2) smallSet
      (S.measure (t_seq n) : Measure ℝ) :=
    levy_foundations_aux_integrableOn_sq_smallSet _
  have hdom : ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) ≤
      ∫ x in smallSet, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) :=
    setIntegral_mono_set hint_sq_small (ae_of_all _ fun x => sq_nonneg x)
      (LE.le.eventuallyLE hsubset)
  have hS : |(t_seq n).val⁻¹ *
      ∫ x in {x | |x| < r}, (x - Real.sin x) ∂(S.measure (t_seq n) : Measure ℝ)| ≤ C₂ := by
    have habs_bound : ∀ x ∈ {x : ℝ | |x| < r}, |x - Real.sin x| ≤ x ^ 2 / 2 :=
      fun x hx => levy_foundations_aux_abs_sub_sin_le_sq_div_two (le_of_lt (lt_of_lt_of_le hx hr1))
    have hxsin_norm : ‖∫ x in {x | |x| < r}, (x - Real.sin x)
          ∂(S.measure (t_seq n) : Measure ℝ)‖ ≤
        (1/2) * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) := by
      calc ‖∫ x in {x | |x| < r}, (x - Real.sin x) ∂(S.measure (t_seq n) : Measure ℝ)‖
          ≤ ∫ x in {x | |x| < r}, ‖x - Real.sin x‖ ∂(S.measure (t_seq n) : Measure ℝ) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in {x | |x| < r}, x ^ 2 / 2 ∂(S.measure (t_seq n) : Measure ℝ) := by
            apply setIntegral_mono_on hint_xsin_small.norm
            · exact ((hint_sq_small.mono_set hsubset).div_const 2)
            · exact hmeas_ball
            · intro x hx
              simp only [Real.norm_eq_abs]
              exact habs_bound x hx
        _ = (1/2) * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) := by
            rw [← integral_const_mul]; congr 1; funext x; ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr t_pos)] at *
    calc (t_seq n).val⁻¹ *
          ‖∫ x in {x | |x| < r}, (x - Real.sin x) ∂(S.measure (t_seq n) : Measure ℝ)‖
        ≤ (t_seq n).val⁻¹ *
            ((1/2) * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ)) :=
          mul_le_mul_of_nonneg_left hxsin_norm (inv_nonneg.mpr (le_of_lt t_pos))
      _ = (1/2) * ((t_seq n).val⁻¹ *
            ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ)) := by ring
      _ ≤ (1/2) * ((t_seq n).val⁻¹ *
            ∫ x in smallSet, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hdom (inv_nonneg.mpr (le_of_lt t_pos))
      _ ≤ (1/2) * C₂ := by
          apply mul_le_mul_of_nonneg_left hC₂n (by norm_num)
      _ ≤ C₂ := by linarith [hC₂_pos]

  exact hS
