-- Prove2me | solution 1 for levy_foundations_public_semigroup_scaled_sine_eventually_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:16:27.41629+00:00
-- url     : https://prove2.me/submissions/fc81ce67-056f-4379-a84f-217793cd94e2

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal

/-- The characteristic-function exponential integrand is bounded and integrable. -/
private lemma levy_foundations_aux_integrable_charFun_integrand
    {μ : Measure ℝ} [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => exp ((↑(ξ * x) : ℂ) * I)) μ :=
  Integrable.of_bound
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id')).mul_const I
      |>.cexp.aestronglyMeasurable)
    1 (ae_of_all _ fun _ => le_of_eq (Complex.norm_exp_ofReal_mul_I _))

/-- The derivative of the complex exponential gives the real first-order
exponential quotient without importing the private source-file lemma. -/
private lemma levy_foundations_aux_exp_first_order (z : ℂ) :
    Tendsto (fun t : ℝ => (exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 z) := by
  have hg : HasDerivAt (fun t : ℝ => cexp ((↑t : ℂ) * z)) z 0 := by
    have hf : HasDerivAt (fun t : ℝ => (↑t : ℂ) * z) (1 * z) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z
    have hexp := hf.cexp
    simp only [ofReal_zero, zero_mul, exp_zero, one_mul, one_mul] at hexp
    exact hexp
  have hslope := hg.tendsto_slope_zero
  simp only [zero_add, ofReal_zero, zero_mul, exp_zero] at hslope
  exact hslope.congr (fun t => by
    show t⁻¹ • (cexp ((↑t : ℂ) * z) - 1) =
      (cexp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)
    rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
    push_cast
    rw [inv_mul_eq_div]
    norm_cast)

/-- Eventual bound from the semigroup characteristic-function imaginary part. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      |(t_seq n).val⁻¹ * ∫ x, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ)| ≤ C := by
  have htseq_filter : Tendsto t_seq atTop (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    rw [Filter.tendsto_comap_iff]
    exact tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall (fun n => (t_seq n).prop)⟩
  have hcf_tend : Tendsto
      (fun n => ((S.measure (t_seq n)).characteristicFun 1 - 1) / ↑(t_seq n).val)
      atTop (𝓝 (S.exponent 1)) := by
    have hbase : Tendsto (fun t : {t : ℝ // 0 < t} =>
        (exp ((↑t.val : ℂ) * S.exponent 1) - 1) / (↑t.val : ℂ))
        (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (S.exponent 1)) :=
      (levy_foundations_aux_exp_first_order (S.exponent 1)).comp
        (tendsto_comap.mono_right (nhdsGT_le_nhdsNE 0) :
          Tendsto Subtype.val
            (Filter.comap Subtype.val (𝓝[>] (0 : ℝ)))
            (𝓝[≠] (0 : ℝ)))
    exact (hbase.comp htseq_filter).congr (fun n => by
      rw [S.charFun_eq (t_seq n) 1]
      rfl)
  have hIm_tend : Tendsto
      (fun n => (((S.measure (t_seq n)).characteristicFun 1 - 1) / ↑(t_seq n).val).im)
      atTop (𝓝 (S.exponent 1).im) :=
    (Complex.continuous_im.tendsto _).comp hcf_tend
  have hIm_bdd : ∀ᶠ n in atTop, |(((S.measure (t_seq n)).characteristicFun 1 - 1) /
      ↑(t_seq n).val).im| ≤ |(S.exponent 1).im| + 1 := by
    have h := hIm_tend.eventually (Metric.ball_mem_nhds (S.exponent 1).im one_pos)
    filter_upwards [h] with n hn
    simp only [Real.dist_eq] at hn
    linarith [abs_sub_abs_le_abs_sub
      (((S.measure (t_seq n)).characteristicFun 1 - 1) / ↑(t_seq n).val).im
      (S.exponent 1).im]
  have hIm_eq : ∀ n,
      (((S.measure (t_seq n)).characteristicFun 1 - 1) / ↑(t_seq n).val).im =
      (t_seq n).val⁻¹ * ∫ x, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ) := by
    intro n
    set t := (t_seq n).val
    set μ : Measure ℝ := (S.measure (t_seq n) : Measure ℝ)
    haveI : IsProbabilityMeasure μ := (S.measure (t_seq n)).prop
    have hcf : charFun μ (1 : ℝ) = ∫ x : ℝ, Complex.exp (↑x * I) ∂μ := by
      rw [charFun_apply_real]; congr 1; ext x; push_cast; ring_nf
    have hint1 : Integrable (fun x : ℝ => Complex.exp (↑x * I)) μ := by
      convert levy_foundations_aux_integrable_charFun_integrand (μ := μ) 1 using 2; push_cast; ring_nf
    have hnum : charFun μ (1 : ℝ) - 1 = ∫ x : ℝ, (Complex.exp (↑x * I) - 1) ∂μ := by
      rw [hcf]
      conv_lhs => rw [show (1 : ℂ) = ∫ _ : ℝ, (1 : ℂ) ∂μ by simp [integral_const]]
      rw [← integral_sub hint1 (integrable_const 1)]
    rw [ProbabilityMeasure.characteristicFun_def, hnum, Complex.div_ofReal_im,
        show (∫ x : ℝ, (Complex.exp (↑x * I) - 1) ∂μ).im =
            ∫ x : ℝ, (Complex.exp (↑x * I) - 1).im ∂μ from
            ((RCLike.imCLM (K := ℂ)).integral_comp_comm
              (hint1.sub (integrable_const 1))).symm]
    simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.exp_ofReal_mul_I_im]
    rw [div_eq_inv_mul]

  refine ⟨|(S.exponent 1).im| + 1, ?_⟩
  filter_upwards [hIm_bdd] with n hn
  simpa only [hIm_eq n] using hn
