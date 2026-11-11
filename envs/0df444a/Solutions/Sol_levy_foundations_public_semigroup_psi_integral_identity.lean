-- Prove2me | solution 1 for levy_foundations_public_semigroup_psi_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:48:34.055786+00:00
-- url     : https://prove2.me/submissions/2131f0d2-3f53-4840-a7c5-266e8db788e6

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat31_drift_term
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_scaled_smallBall_compensated_tendsto
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_scaled_largeSet_charFun_tendsto
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat30_charFun_sub_one_div_decomp
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat29_psi_algebra

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

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

/-- Recover the semigroup exponent by splitting its scaled characteristic
function into drift, compensated small jumps, and large jumps. The
large-jump convergence is the sole remaining analytic input. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : r ∈ Set.Ioc (1 / 2 : ℝ) 1)
    (b_r : ℝ) (σ_sq_r : ℝ≥0)
    {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht_seq : Tendsto (fun n => (t_seq n).val) atTop (𝓝 (0 : ℝ)))
    (hb : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 b_r))
    (hσ : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 (σ_sq_r : ℝ)))
    (h_jump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
      Tendsto (fun n => (t_seq n).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
        atTop (𝓝 (∫ x, f x ∂ν)))
    (ξ : ℝ) :
    S.exponent ξ =
      ↑(b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν) * ↑ξ * I
      - ↑((σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν) * ↑ξ ^ 2 / 2
      + ∫ x, levyCompensatedIntegrand ξ x ∂ν := by
  have hr_pos : (0 : ℝ) < r := by linarith [hr.1]
  have htseq_filter : Tendsto t_seq atTop (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    rw [Filter.tendsto_comap_iff]
    exact tendsto_nhdsWithin_iff.mpr
      ⟨ht_seq, Filter.Eventually.of_forall (fun n => (t_seq n).prop)⟩
  have hLHS : Tendsto (fun n =>
      (charFun (S.measure (t_seq n) : Measure ℝ) ξ - 1) / (↑(t_seq n).val : ℂ))
      atTop (𝓝 (S.exponent ξ)) :=
    by
      have hbase : Tendsto (fun t : {t : ℝ // 0 < t} =>
          (exp ((↑t.val : ℂ) * S.exponent ξ) - 1) / (↑t.val : ℂ))
          (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (S.exponent ξ)) :=
        (levy_foundations_aux_exp_first_order (S.exponent ξ)).comp
          (tendsto_comap.mono_right (nhdsGT_le_nhdsNE 0) :
            Tendsto Subtype.val
              (Filter.comap Subtype.val (𝓝[>] (0 : ℝ)))
              (𝓝[≠] (0 : ℝ)))
      exact (hbase.comp htseq_filter).congr (fun n => by
        rw [← ProbabilityMeasure.characteristicFun_def,
          S.charFun_eq (t_seq n) ξ]
        rfl)
  have hT1 := S.leanlevy_chat31_drift_term ξ ht_seq hb
  have hT2 := S.leanlevy_chat33_scaled_smallBall_compensated_tendsto
    hr_pos hr.2 ξ hν hν_r hσ h_jump
  have hT3 := S.leanlevy_chat33_scaled_largeSet_charFun_tendsto
    hr_pos ξ hν hν_r h_jump
  have hRHS_lim := (hT1.add hT2).add hT3
  have hLHS_sum := hLHS.congr (fun n => by
    rw [S.leanlevy_chat30_charFun_sub_one_div_decomp (t_seq n) ξ hr.2,
      Complex.ofReal_inv])
  have h_eq := tendsto_nhds_unique hLHS_sum hRHS_lim
  rw [h_eq]
  exact ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat29_psi_algebra
    hr ξ hν b_r σ_sq_r