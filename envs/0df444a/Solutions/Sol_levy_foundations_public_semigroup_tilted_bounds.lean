-- Prove2me | solution 1 for levy_foundations_public_semigroup_tilted_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:54:46.413935+00:00
-- url     : https://prove2.me/submissions/164614da-fdf7-45d8-9137-e10d530d7bae

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_second_moment_eventually_bounded
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_mass_bound
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_uniform_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Decompose the bounded tilt min(1,x²) into the unit small ball and its complement. -/
private lemma levy_foundations_tilt_integral_split
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ x, min (1 : ℝ) (x ^ 2) ∂μ) =
      (∫ x in smallSet, x ^ 2 ∂μ) + (μ (largeSet 1)).toReal := by
  have hsmall : MeasurableSet smallSet :=
    (isOpen_Iio.preimage continuous_abs).measurableSet
  have hlarge : MeasurableSet (largeSet (1 : ℝ)) :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hcomp : smallSetᶜ = largeSet (1 : ℝ) := by
    ext x
    change (¬ |x| < 1) ↔ 1 ≤ |x|
    exact not_lt
  have hint : Integrable (fun x : ℝ => min (1 : ℝ) (x ^ 2)) μ :=
    Integrable.of_bound
      (continuous_const.min (continuous_pow 2)).aestronglyMeasurable 1
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (le_min (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg x))]
        exact min_le_left _ _)
  have hsmall_eq : (∫ x in smallSet, min (1 : ℝ) (x ^ 2) ∂μ) =
      (∫ x in smallSet, x ^ 2 ∂μ) := by
    apply setIntegral_congr_fun hsmall
    intro x hx
    have hxlt : |x| < 1 := (show x ∈ smallSet ↔ |x| < 1 from Iff.rfl).mp hx
    have hsq : x ^ 2 ≤ 1 := by
      have hpow : |x| ^ 2 < 1 :=
        pow_lt_one₀ (abs_nonneg x) hxlt two_ne_zero
      exact le_of_lt (by simpa only [sq_abs] using hpow)
    exact min_eq_right hsq
  have hlarge_eq : (∫ x in largeSet 1, min (1 : ℝ) (x ^ 2) ∂μ) =
      (μ (largeSet 1)).toReal := by
    have hset : ∀ x ∈ largeSet (1 : ℝ),
        min (1 : ℝ) (x ^ 2) = 1 := by
      intro x hx
      have hxge : 1 ≤ |x| := hx
      have hsq : (1 : ℝ) ≤ x ^ 2 := by
        have hpow : (1 : ℝ) ≤ |x| ^ 2 := by
          nlinarith [abs_nonneg x]
        simpa only [sq_abs] using hpow
      exact min_eq_left hsq
    rw [setIntegral_congr_fun hlarge hset]
    simp only [setIntegral_const, smul_eq_mul, one_mul, mul_one, Measure.real_def]
  have hs := integral_add_compl hsmall hint
  rw [hcomp, hsmall_eq, hlarge_eq] at hs
  exact hs.symm

/-- The uniform weighted bound follows from separate second-moment and tail-mass budgets. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 (0 : ℝ)) ∧
      (∃ C : ℝ, ∀ n,
        (t_seq n).val⁻¹ *
          ∫ x, min (1 : ℝ) (x ^ 2) ∂(S.measure (t_seq n) : Measure ℝ) ≤ C) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧
        ∀ n,
          (t_seq n).val⁻¹ *
            ((S.measure (t_seq n) : Measure ℝ) (largeSet R)).toReal ≤ δ) := by
  let base : ℕ → {t : ℝ // 0 < t} :=
    fun n => ⟨(1 / 2 : ℝ) ^ n, pow_pos (by norm_num) n⟩
  have htbase : Tendsto (fun n => (base n).val) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    levy_foundations_public_semigroup_second_moment_eventually_bounded S htbase
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hC₂
  let t_seq : ℕ → {t : ℝ // 0 < t} := fun n => base (n + N)
  have htseq : Tendsto (fun n => (t_seq n).val) atTop (𝓝 (0 : ℝ)) :=
    htbase.comp (Filter.tendsto_add_atTop_nat N)
  obtain ⟨Cmass, hmass⟩ :=
    levy_foundations_public_semigroup_scaled_largeSet_mass_bound S 1 (by norm_num)
  refine ⟨t_seq, htseq, ⟨C₂ + (Cmass : ℝ), ?_⟩, ?_⟩
  · intro n
    haveI : IsProbabilityMeasure (S.measure (t_seq n) : Measure ℝ) :=
      (S.measure (t_seq n)).prop
    have hsq := hN (n + N) (by omega : N ≤ n + N)
    have hlarge := hmass (t_seq n)
    change (t_seq n).val⁻¹ *
      ((S.measure (t_seq n) : Measure ℝ) (largeSet 1)).toReal ≤
        (Cmass : ℝ) at hlarge
    rw [levy_foundations_tilt_integral_split]
    ring_nf
    exact add_le_add hsq hlarge
  · intro δ hδ
    obtain ⟨R, hR, hRall⟩ :=
      levy_foundations_public_semigroup_scaled_largeSet_uniform_tail S δ hδ
    exact ⟨R, hR, fun n => hRall (t_seq n)⟩
