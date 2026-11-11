-- Prove2me | solution 1 for levy_foundations_public_semigroup_scaled_largeSet_sharp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:23:22.982552+00:00
-- url     : https://prove2.me/submissions/fcefd700-eb24-4bdd-aeae-ed102a58f551

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_largeSet_cosine_interval_lower_bound
import Theorems.Thm_levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
import Theorems.Thm_levy_foundations_public_cosine_interval_integral_swap
import Theorems.Thm_levy_foundations_public_semigroup_real_deficit_cosine_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal

/-- Uniform large-set scaled mass via Fourier smoothing and the semigroup exponent bound. -/
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ,
      (∀ ξ ∈ Set.Icc (0 : ℝ) (2 / ε), ‖S.exponent ξ‖ ≤ M) ∧
      ∀ t : {t : ℝ // 0 < t},
        t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet ε)).toReal ≤ 4 * M := by
  obtain ⟨ξ_max, -, hξ_max⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, Set.left_mem_Icc.mpr (by positivity)⟩ : (Set.Icc (0:ℝ) (2/ε)).Nonempty)
    S.exponent_continuous.norm.continuousOn
  set M := ‖S.exponent ξ_max‖ with hM_def
  have hkey : ∀ ξ ∈ Set.Icc (0:ℝ) (2/ε), ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * M := by
    intro ξ hξ t
    have hξM : ‖S.exponent ξ‖ ≤ M := hξ_max hξ
    exact (levy_foundations_public_semigroup_scaled_exponential_real_norm_bound S t ξ).trans
      (by linarith)
  refine ⟨M, hξ_max, fun t => ?_⟩
  set μ := (S.measure t : Measure ℝ)
  haveI : IsProbabilityMeasure μ := (S.measure t).property
  have h_nn : ∀ (ξ x : ℝ), 0 ≤ 1 - Real.cos (ξ * x) := fun ξ x => sub_nonneg.mpr (Real.cos_le_one _)
  have hfubini := levy_foundations_public_cosine_interval_integral_swap μ ε hε
  have hrhs : (∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ) =
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    congr 1; ext ξ
    exact (levy_foundations_public_semigroup_real_deficit_cosine_integral S t ξ).symm
  have h_intcont : Continuous (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x ξ => 1 - Real.cos (ξ * x))
      (by fun_prop) 0 (2/ε)
  have hint_outer : Integrable (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) μ :=
    Integrable.of_bound
      h_intcont.aestronglyMeasurable
      (4/ε)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
            (intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)]
        have hfx_int : IntervalIntegrable (fun ξ => 1 - Real.cos (ξ * x)) volume 0 (2/ε) :=
          (continuous_const.sub (Real.continuous_cos.comp
            (continuous_id.mul continuous_const))).intervalIntegrable 0 (2/ε)
        calc ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))
            ≤ ∫ ξ in (0:ℝ)..(2/ε), (2 : ℝ) :=
              intervalIntegral.integral_mono_on (by positivity) hfx_int intervalIntegrable_const
                (fun ξ _ => by linarith [Real.neg_one_le_cos (ξ * x)])
          _ = 4/ε := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              field_simp; ring)
  have hpointwise : ∀ x ∈ largeSet ε,
      ε⁻¹ ≤ ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) := by
    intro x hx
    exact levy_foundations_public_largeSet_cosine_interval_lower_bound ε hε x
      ((show x ∈ largeSet ε ↔ ε ≤ |x| from Iff.rfl).mp hx)
  have hmass : ε⁻¹ * (μ (largeSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    rw [← hrhs, hfubini]
    rw [show ε⁻¹ * (μ (largeSet ε)).toReal =
      ∫ _ in largeSet ε, ε⁻¹ ∂μ by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, mul_comm]]
    exact le_trans
      (setIntegral_mono_on integrableOn_const hint_outer.integrableOn
        ((measurableSet_le measurable_const continuous_abs.measurable)) (fun x hx => hpointwise x hx))
      (setIntegral_le_integral hint_outer (ae_of_all _ (fun x =>
        intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)))
  have ht_inv_nn : 0 ≤ t.val⁻¹ := le_of_lt (inv_pos.mpr t.prop)
  have hmass_t : t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    have hrearrange : t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal =
        t.val⁻¹ * (ε⁻¹ * (μ (largeSet ε)).toReal) := by ring
    rw [hrearrange]
    calc t.val⁻¹ * (ε⁻¹ * (μ (largeSet ε)).toReal)
        ≤ t.val⁻¹ * (∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) :=
          mul_le_mul_of_nonneg_left hmass ht_inv_nn
      _ = ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re := by
          rw [← intervalIntegral.integral_const_mul]
  have hint_exp : IntervalIntegrable
      (fun ξ => t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re) volume 0 (2/ε) :=
    ((continuous_const.sub
        (Complex.continuous_re.comp
          (Complex.continuous_exp.comp
            (continuous_const.mul S.exponent_continuous)))).const_mul _).intervalIntegrable _ _
  have hint_2M : ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤
      ∫ ξ in (0:ℝ)..(2/ε), (2 * M) :=
    intervalIntegral.integral_mono_on (by positivity) hint_exp intervalIntegrable_const
      (fun ξ hξ => hkey ξ hξ t)
  have hint_const : ∫ ξ in (0:ℝ)..(2/ε), (2 * M) = 4 * M / ε := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp [hε.ne']
    ring
  calc t.val⁻¹ * (μ (largeSet ε)).toReal
      = ε * (t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal) := by field_simp [hε.ne', ne_of_gt t.prop]
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) := by
        exact mul_le_mul_of_nonneg_left hmass_t (le_of_lt hε)
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), (2 * M)) := by
        apply mul_le_mul_of_nonneg_left hint_2M (le_of_lt hε)
    _ = ε * (4 * M / ε) := by rw [hint_const]
    _ = 4 * M := by field_simp [hε.ne']
