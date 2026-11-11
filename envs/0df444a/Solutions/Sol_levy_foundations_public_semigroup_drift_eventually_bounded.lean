-- Prove2me | solution 1 for levy_foundations_public_semigroup_drift_eventually_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:12:54.915414+00:00
-- url     : https://prove2.me/submissions/8e6ed211-7d97-493c-8df7-543c7b63dcb7

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_scaled_sine_eventually_bounded
import Theorems.Thm_levy_foundations_public_semigroup_scaled_small_sine_error_eventually_bounded
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_mass_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Bound the small-ball drift by the full sine, small sine error and tail sine. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      ((t_seq n).val⁻¹ *
        ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
        ∈ Set.Icc (-C) C := by
  obtain ⟨C₁, hC₁⟩ :=
    levy_foundations_public_semigroup_scaled_sine_eventually_bounded S ht
  obtain ⟨C₂, hC₂⟩ :=
    levy_foundations_public_semigroup_scaled_small_sine_error_eventually_bounded S hr hr1 ht
  obtain ⟨C₃, hC₃⟩ :=
    levy_foundations_public_semigroup_scaled_largeSet_mass_bound S r hr
  refine ⟨C₁ + C₂ + (C₃ : ℝ), ?_⟩
  filter_upwards [hC₁, hC₂] with n hn₁ hn₂
  let μ : Measure ℝ := (S.measure (t_seq n) : Measure ℝ)
  haveI : IsProbabilityMeasure μ := (S.measure (t_seq n)).prop
  have ht_pos : 0 < (t_seq n).val := (t_seq n).prop
  have hmeas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hball_compl : {x : ℝ | |x| < r} = (largeSet r)ᶜ := by
    ext x
    simp only [largeSet, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hint_sin : Integrable (fun x => Real.sin x) μ :=
    Integrable.of_bound Real.continuous_sin.aestronglyMeasurable 1
      (ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩)
  have hint_x_ball : IntegrableOn (fun x => x) {x | |x| < r} μ :=
    IntegrableOn.of_bound (measure_lt_top _ _)
      continuous_id.aestronglyMeasurable.restrict 1
      ((ae_restrict_mem hmeas_ball).mono (fun x hx => by
        simp only [Real.norm_eq_abs]
        exact (lt_of_lt_of_le hx hr1).le))
  have hint_sin_ball : IntegrableOn (fun x => Real.sin x) {x | |x| < r} μ :=
    hint_sin.integrableOn
  have hsplit_x :
      ∫ x in {x | |x| < r}, x ∂μ =
        (∫ x in {x | |x| < r}, (x - Real.sin x) ∂μ) +
        ∫ x in {x | |x| < r}, Real.sin x ∂μ := by
    calc
      (∫ x in {x | |x| < r}, x ∂μ) =
          ∫ x in {x | |x| < r}, ((x - Real.sin x) + Real.sin x) ∂μ := by
            congr 1
            ext x
            ring
      _ = (∫ x in {x | |x| < r}, (x - Real.sin x) ∂μ) +
            ∫ x in {x | |x| < r}, Real.sin x ∂μ := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            (integral_add (hint_x_ball.sub hint_sin_ball) hint_sin_ball)
  have hsplit_sin :
      ∫ x in {x | |x| < r}, Real.sin x ∂μ =
        ∫ x, Real.sin x ∂μ - ∫ x in largeSet r, Real.sin x ∂μ := by
    have hlarge_meas : MeasurableSet (largeSet r) := by
      change MeasurableSet {x : ℝ | r ≤ |x|}
      exact measurableSet_le measurable_const continuous_abs.measurable
    rw [hball_compl, ← integral_add_compl hlarge_meas hint_sin]
    ring
  have htail :
      |(t_seq n).val⁻¹ * ∫ x in largeSet r, Real.sin x ∂μ| ≤ (C₃ : ℝ) := by
    have hbound :
        ‖∫ x in largeSet r, Real.sin x ∂μ‖ ≤ (μ (largeSet r)).toReal := by
      have h := norm_setIntegral_le_of_norm_le_const
        (measure_lt_top μ (largeSet r))
        (fun x _ => show ‖Real.sin x‖ ≤ 1 by
          simp only [Real.norm_eq_abs]
          exact abs_le.mpr ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩)
      simpa [one_mul, measureReal_def] using h
    rw [abs_mul, abs_of_pos (inv_pos.mpr ht_pos)]
    calc
      (t_seq n).val⁻¹ * |∫ x in largeSet r, Real.sin x ∂μ|
          ≤ (t_seq n).val⁻¹ * (μ (largeSet r)).toReal := by
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht_pos.le)
            rwa [Real.norm_eq_abs] at hbound
      _ ≤ (C₃ : ℝ) := hC₃ (t_seq n)
  have hrewrite :
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂μ =
      ((t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, (x - Real.sin x) ∂μ) +
      ((t_seq n).val⁻¹ * ∫ x, Real.sin x ∂μ) -
      ((t_seq n).val⁻¹ * ∫ x in largeSet r, Real.sin x ∂μ) := by
    rw [hsplit_x, hsplit_sin]
    ring
  let A : ℝ := (t_seq n).val⁻¹ *
    ∫ x in {x | |x| < r}, (x - Real.sin x) ∂μ
  let B : ℝ := (t_seq n).val⁻¹ * ∫ x, Real.sin x ∂μ
  let D : ℝ := (t_seq n).val⁻¹ * ∫ x in largeSet r, Real.sin x ∂μ
  have hA : |A| ≤ C₂ := hn₂
  have hB : |B| ≤ C₁ := hn₁
  have hD : |D| ≤ (C₃ : ℝ) := htail
  have htri : |A + B - D| ≤ |A| + |B| + |D| := by
    have h1 := abs_add_le A B
    have h2 := abs_add_le (A + B) (-D)
    rw [abs_neg] at h2
    simp only [sub_eq_add_neg]
    linarith
  have hnorm :
      |(t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂μ| ≤
        C₁ + C₂ + (C₃ : ℝ) := by
    rw [hrewrite]
    change |A + B - D| ≤ C₁ + C₂ + (C₃ : ℝ)
    linarith
  exact abs_le.mp hnorm
