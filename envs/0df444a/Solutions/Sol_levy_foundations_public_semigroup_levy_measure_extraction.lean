-- Prove2me | solution 1 for levy_foundations_public_semigroup_levy_measure_extraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:25:16.927583+00:00
-- url     : https://prove2.me/submissions/03b2784d-7b58-41a0-bc57-eef3668b4e24

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_canonical_measure_extraction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section
/-- The untilting density is positive off zero. -/
private lemma levy_public_min_one_sq_pos_of_ne_zero {x : ℝ} (hx : x ≠ 0) : 0 < min 1 (x ^ 2) :=
  lt_min one_pos (by rw [← sq_abs]; exact pow_pos (abs_pos.mpr hx) 2)
/-- Real integration against a tilted scaled measure. -/
private lemma levy_public_tiltedScaledMeasure_integral_eq
    (S : ProbabilityTheory.ConvolutionSemigroup) (t : {t : ℝ // 0 < t}) (g : ℝ → ℝ) :
    ∫ x, g x ∂(S.tiltedScaledMeasure t) =
      t.val⁻¹ * ∫ x, g x * min 1 (x ^ 2) ∂(S.measure t : Measure ℝ) := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (continuous_pow 2).measurable)
  have hpt : ∀ x : ℝ, (ENNReal.ofReal (min 1 (x ^ 2))).toReal • g x = g x * min 1 (x ^ 2) := by
    intro x
    rw [ENNReal.toReal_ofReal (le_min zero_le_one (sq_nonneg x)), smul_eq_mul, mul_comm]
  rw [show S.tiltedScaledMeasure t = (S.scaledMeasure t).withDensity
        (fun x => ENNReal.ofReal (min 1 (x ^ 2))) from rfl,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_congr_ae (Eventually.of_forall hpt),
    show S.scaledMeasure t = ENNReal.ofReal t.val⁻¹ • (S.measure t : Measure ℝ) from rfl,
    integral_smul_measure,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr t.prop)), smul_eq_mul]
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (ν : Measure ℝ), IsLevyMeasure ν ∧
      ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
        Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
        (∀ (f : BoundedContinuousFunction ℝ ℝ), (∃ r > 0, ∀ x, |x| < r → f x = 0) →
          Tendsto (fun n => (t_seq n).val⁻¹ *
              ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
            atTop (𝓝 (∫ x, f x ∂ν))) := by
  obtain ⟨η, hη_fin, t_seq, ht_seq_tendsto, hconv⟩ := levy_foundations_public_semigroup_canonical_measure_extraction S
  haveI : IsFiniteMeasure η := hη_fin
  have hmin_meas : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) := ENNReal.measurable_ofReal.comp (measurable_const.min (continuous_pow 2).measurable)
  have hdens_meas : Measurable (fun x : ℝ => (ENNReal.ofReal (min 1 (x ^ 2)))⁻¹) := hmin_meas.inv
  let ν : Measure ℝ :=
    (η.restrict {0}ᶜ).withDensity (fun x => (ENNReal.ofReal (min 1 (x ^ 2)))⁻¹)
  have hbase0 : (η.restrict {0}ᶜ) {0} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    simp
  have hν_zero : ν {0} = 0 := by
    simp only [ν]
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ hbase0
  have hdens_ae_lt : ∀ᵐ x ∂(η.restrict {0}ᶜ), (ENNReal.ofReal (min 1 (x ^ 2)))⁻¹ < ⊤ := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton 0).compl] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hpos : 0 < min 1 (x ^ 2) :=
      levy_public_min_one_sq_pos_of_ne_zero hx0
    rw [ENNReal.inv_lt_top]
    exact ENNReal.ofReal_pos.mpr hpos
  have hprod_ae :
      (fun x => (ENNReal.ofReal (min 1 (x ^ 2)))⁻¹ * ENNReal.ofReal (min 1 (x ^ 2)))
        =ᵐ[η.restrict {0}ᶜ] (fun _ => 1) := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton 0).compl] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hpos : 0 < min 1 (x ^ 2) :=
      levy_public_min_one_sq_pos_of_ne_zero hx0
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top
  have hν_int : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤ := by
    simp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul _ hdens_meas hmin_meas]
    simp only [Pi.mul_apply]
    rw [lintegral_congr_ae hprod_ae, lintegral_one]
    calc (η.restrict {0}ᶜ) Set.univ = η {0}ᶜ := Measure.restrict_apply_univ _
      _ ≤ η Set.univ := measure_mono (Set.subset_univ _)
      _ < ⊤ := measure_lt_top η Set.univ
  have hν_levy : IsLevyMeasure ν := ⟨hν_zero, hν_int⟩
  refine ⟨ν, hν_levy, t_seq, ht_seq_tendsto, ?_⟩
  intro f hf
  obtain ⟨r, hr_pos, hf_zero⟩ := hf
  have hcont : Continuous (fun x : ℝ => f x / min 1 (x ^ 2)) := by
    rw [continuous_iff_continuousAt]
    intro x₀
    by_cases hx₀ : |x₀| < r
    · have hmem : {y : ℝ | |y| < r} ∈ 𝓝 x₀ :=
        (isOpen_lt continuous_abs continuous_const).mem_nhds hx₀
      have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x₀] (fun x => f x / min 1 (x ^ 2)) := by
        filter_upwards [hmem] with y hy
        rw [hf_zero y hy, zero_div]
      exact continuousAt_const.congr heq
    · push Not at hx₀
      have hx0_ne : x₀ ≠ 0 := by rintro rfl; rw [abs_zero] at hx₀; linarith
      have hden_ne : min 1 (x₀ ^ 2) ≠ 0 :=
        ne_of_gt (levy_public_min_one_sq_pos_of_ne_zero hx0_ne)
      exact f.continuous.continuousAt.div
        ((continuous_const.min (continuous_pow 2)).continuousAt) hden_ne
  have hbound : ∀ x, ‖f x / min 1 (x ^ 2)‖ ≤ ‖f‖ / min 1 (r ^ 2) := by
    intro x
    rw [Real.norm_eq_abs]
    have hden_r_pos : 0 < min 1 (r ^ 2) := lt_min one_pos (by positivity)
    by_cases hx : |x| < r
    · rw [hf_zero x hx, zero_div, abs_zero]; positivity
    · push Not at hx
      have hxr2 : r ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, hx, hr_pos.le, abs_nonneg x]
      have hmono : min 1 (r ^ 2) ≤ min 1 (x ^ 2) := min_le_min le_rfl hxr2
      have hden_x_pos : 0 < min 1 (x ^ 2) := lt_of_lt_of_le hden_r_pos hmono
      have hfx : |f x| ≤ ‖f‖ := by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x
      rw [abs_div, abs_of_pos hden_x_pos, div_le_div_iff₀ hden_x_pos hden_r_pos]
      exact mul_le_mul hfx hmono hden_r_pos.le (norm_nonneg f)
  let G : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f x / min 1 (x ^ 2)) hcont
      (‖f‖ / min 1 (r ^ 2)) hbound
  have hG_apply : ∀ x, G x = f x / min 1 (x ^ 2) := fun _ => rfl
  have hG0 : G 0 = 0 := by
    rw [hG_apply, hf_zero 0 (by simpa using hr_pos), zero_div]
  have hfg_pt : ∀ x, (f x : ℝ) = G x * min 1 (x ^ 2) := by
    intro x
    rw [hG_apply x]
    by_cases hx : |x| < r
    · rw [hf_zero x hx, zero_div, zero_mul]
    · push Not at hx
      have hx0 : x ≠ 0 := by rintro rfl; rw [abs_zero] at hx; linarith
      have hden_ne : min 1 (x ^ 2) ≠ 0 :=
        ne_of_gt (levy_public_min_one_sq_pos_of_ne_zero hx0)
      rw [div_mul_cancel₀ _ hden_ne]
  have hLHS : ∀ n, (t_seq n).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ)
      = ∫ x, G x ∂(S.tiltedScaledMeasure (t_seq n)) := by
    intro n
    rw [levy_public_tiltedScaledMeasure_integral_eq S (t_seq n) (fun x => G x)]
    congr 1
    exact integral_congr_ae (ae_of_all _ hfg_pt)
  have hstep2 : ∫ x, f x ∂ν = ∫ x, G x ∂(η.restrict {0}ᶜ) := by
    simp only [ν]
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_ae_lt]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_singleton 0).compl] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hpos : 0 < min 1 (x ^ 2) :=
      levy_public_min_one_sq_pos_of_ne_zero hx0
    rw [smul_eq_mul, hG_apply x, ENNReal.toReal_inv, ENNReal.toReal_ofReal hpos.le,
        div_eq_inv_mul]
  have hstep1 : ∫ x, G x ∂η = ∫ x, G x ∂(η.restrict {0}ᶜ) := by
    rw [← integral_add_compl (measurableSet_singleton 0) (G.integrable η),
        integral_singleton, hG0, smul_zero, zero_add]
  have hRHS : ∫ x, f x ∂ν = ∫ x, G x ∂η := hstep2.trans hstep1.symm
  rw [hRHS]
  simp_rw [hLHS]
  exact hconv G hG0
