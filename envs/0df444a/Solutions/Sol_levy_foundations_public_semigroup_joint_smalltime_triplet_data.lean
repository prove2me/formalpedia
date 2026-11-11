-- Prove2me | solution 1 for levy_foundations_public_semigroup_joint_smalltime_triplet_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:06:55.025101+00:00
-- url     : https://prove2.me/submissions/8d4fe03b-e2f1-414e-9222-97e529468a54

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_levy_measure_extraction
import Theorems.Thm_levy_foundations_public_semigroup_drift_subsequence
import Theorems.Thm_levy_foundations_public_semigroup_second_moment_eventually_bounded
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_exists_atomFree_radius

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

/-- Joint extraction along one subsequence, after the Lévy measure and drift
subsequence are constructed. -/
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (r : ℝ) (b : ℝ) (σ_sq : ℝ≥0) (ν : Measure ℝ), IsLevyMeasure ν ∧
      ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
      r ∈ Set.Ioc (1/2 : ℝ) 1 ∧
      ν {x | |x| = r} = 0 ∧
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
          atTop (𝓝 b) ∧
      Tendsto (fun n =>
        (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ))
          atTop (𝓝 (σ_sq : ℝ)) ∧
      (∀ (f : BoundedContinuousFunction ℝ ℝ), (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
        Tendsto (fun n => (t_seq n).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) := by
  -- Step 1: Outer extraction — Lévy measure ν and its witnessing sequence t_seq_ν.
  obtain ⟨ν, hν, t_seq_ν, ht_seq_ν, h_jump_conv⟩ := levy_foundations_public_semigroup_levy_measure_extraction S
  -- Step 1b: an atom-free split radius `r ∈ (1/2, 1]`.
  obtain ⟨r, hr_mem, hν_r⟩ :=
    hν.exists_atomFree_radius (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hr_pos : (0 : ℝ) < r := by linarith [hr_mem.1]
  have hr_le1 : r ≤ 1 := hr_mem.2
  have hmeas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hsubset : {x : ℝ | |x| < r} ⊆ smallSet :=
    fun x hx => (show x ∈ smallSet ↔ |x| < 1 from Iff.rfl).mpr (lt_of_lt_of_le hx hr_le1)
  -- Step 2: Drift sub-subsequence φ₁ along t_seq_ν, at radius r.
  obtain ⟨b, φ₁, hφ₁_mono, hb⟩ := levy_foundations_public_semigroup_drift_subsequence S hr_pos hr_le1 ht_seq_ν
  -- The composed sequence t_seq_ν ∘ φ₁ still tends to 0.
  have ht_seq₁ : Tendsto (fun n => (t_seq_ν (φ₁ n)).val) atTop (𝓝 0) :=
    ht_seq_ν.comp hφ₁_mono.tendsto_atTop
  -- Step 3: Variance sub-sub-subsequence φ₂ via Bolzano-Weierstrass on Icc 0 C.
  obtain ⟨C, _hC_pos, hC⟩ := levy_foundations_public_semigroup_second_moment_eventually_bounded S ht_seq₁
  set a : ℕ → ℝ := fun n =>
    (t_seq_ν (φ₁ n)).val⁻¹ *
      ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) with ha_def
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n => by
    have ht_pos : 0 < (t_seq_ν (φ₁ n)).val := (t_seq_ν (φ₁ n)).prop
    refine mul_nonneg (inv_nonneg.mpr ht_pos.le) ?_
    exact setIntegral_nonneg hmeas_ball (fun x _ => sq_nonneg x)
  have ha_bdd : ∀ᶠ n in atTop, a n ∈ Set.Icc (0 : ℝ) C := by
    filter_upwards [hC] with n hCn
    refine ⟨ha_nonneg n, ?_⟩
    -- a n = t⁻¹∫_{|x|<r} x² ≤ t⁻¹∫_small x² ≤ C  (domination over {|x|<r} ⊆ smallSet).
    have ht_pos : 0 < (t_seq_ν (φ₁ n)).val := (t_seq_ν (φ₁ n)).prop
    have hint_sq_small : IntegrableOn (fun x => x ^ 2) smallSet
        (S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) :=
      levy_foundations_aux_integrableOn_sq_smallSet _
    have hdom : ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) ≤
        ∫ x in smallSet, x ^ 2 ∂(S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) :=
      setIntegral_mono_set hint_sq_small (ae_of_all _ fun x => sq_nonneg x)
        (LE.le.eventuallyLE hsubset)
    calc a n
        ≤ (t_seq_ν (φ₁ n)).val⁻¹ *
            ∫ x in smallSet, x ^ 2 ∂(S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) :=
          mul_le_mul_of_nonneg_left hdom (inv_nonneg.mpr ht_pos.le)
      _ ≤ C := hCn
  obtain ⟨σ, hσ_mem, φ₂, hφ₂_mono, hσ⟩ :=
    isCompact_Icc.tendsto_subseq' ha_bdd.frequently
  -- Step 4: Assemble the final subsequence t_seq_ν ∘ φ₁ ∘ φ₂.
  set t_seq : ℕ → {t : ℝ // 0 < t} := fun n => t_seq_ν (φ₁ (φ₂ n)) with ht_seq_def
  -- t_seq tends to 0.
  have ht_seq : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) :=
    ht_seq₁.comp hφ₂_mono.tendsto_atTop
  -- Drift convergence along the composite subsequence (at radius r).
  have hb_final : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 b) := hb.comp hφ₂_mono.tendsto_atTop
  -- Variance convergence: σ ≥ 0 so it coerces from Real.toNNReal.
  have hσ_final : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 ((Real.toNNReal σ : ℝ≥0) : ℝ)) := by
    rw [Real.coe_toNNReal σ hσ_mem.1]
    exact hσ
  -- Jump-measure convergence: subseq of jump-convergent is still jump-convergent.
  have h_jump_final : ∀ (f : BoundedContinuousFunction ℝ ℝ),
      (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
      Tendsto (fun n => (t_seq n).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
        atTop (𝓝 (∫ x, f x ∂ν)) := by
    intro f hf
    have h := h_jump_conv f hf
    exact h.comp ((hφ₁_mono.comp hφ₂_mono).tendsto_atTop)
  exact ⟨r, b, Real.toNNReal σ, ν, hν, t_seq, hr_mem, hν_r, ht_seq, hb_final,
    hσ_final, h_jump_final⟩
