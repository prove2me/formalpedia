-- Prove2me | solution 1 for levy_foundations_public_canonical_prokhorov_from_tilted_tightness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:38:13.961922+00:00
-- url     : https://prove2.me/submissions/c66cc44b-0190-467e-8642-6a9e724d42be

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_tilted_cofinal_mass_sequence
import Theorems.Thm_levy_foundations_public_prob_topup_normalises
import Mathlib.Probability.Independence.CharacteristicFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder
theorem solution (S : ConvolutionSemigroup) (Cmass : ℝ≥0)
    (hCmass_pos : 0 < Cmass)
    (hCmass_ev : ∀ᶠ (t : {t : ℝ // 0 < t}) in comap Subtype.val (𝓝[>] (0 : ℝ)),
      S.tiltedScaledMeasure t Set.univ ≤ (Cmass : ℝ≥0∞))
    (htail : ∀ (ε : ℝ), 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ (t : {t : ℝ // 0 < t}),
        S.tiltedScaledMeasure t (largeSet R) ≤ ENNReal.ofReal ε) :
    ∃ (η : Measure ℝ) (_ : IsFiniteMeasure η) (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ), f 0 = 0 →
        Tendsto (fun n => ∫ x, f x ∂(S.tiltedScaledMeasure (t_seq n)))
          atTop (𝓝 (∫ x, f x ∂η)) := by
  obtain ⟨t_seq, ht_seq_tendsto, hmass⟩ :=
    levy_foundations_public_tilted_cofinal_mass_sequence S Cmass hCmass_ev
  set ν : ℕ → Measure ℝ := fun n => S.tiltedScaledMeasure (t_seq n) with hν_def
  have hmass_ν : ∀ n, ν n Set.univ ≤ (Cmass : ℝ≥0∞) := hmass
  have hν_finite : ∀ n, IsFiniteMeasure (ν n) := fun n =>
    ⟨lt_of_le_of_lt (hmass_ν n) ENNReal.coe_lt_top⟩
  set Mass : ℝ := (Cmass : ℝ) + 1 with hMass_def
  have hMass_pos : (0 : ℝ) < Mass := by rw [hMass_def]; positivity
  have hMass_ge_one : (1 : ℝ) ≤ Mass := by rw [hMass_def]; exact le_add_of_nonneg_left (NNReal.coe_nonneg Cmass)
  have hν_mass_le_Mass : ∀ n, ν n Set.univ ≤ ENNReal.ofReal Mass := fun n => by
    calc ν n Set.univ ≤ (Cmass : ℝ≥0∞) := hmass_ν n
      _ = ENNReal.ofReal (Cmass : ℝ) := ENNReal.ofReal_coe_nnreal.symm
      _ ≤ ENNReal.ofReal Mass := ENNReal.ofReal_le_ofReal (by rw [hMass_def]; linarith)
  set p_meas : ℕ → Measure ℝ := fun n =>
    (ENNReal.ofReal Mass⁻¹) • ν n +
      (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν n Set.univ)) • Measure.dirac 0 with hp_meas_def
  have hp_prob : ∀ n, IsProbabilityMeasure (p_meas n) := by
    intro n
    exact levy_foundations_public_prob_topup_normalises (ν n) Mass hMass_pos (hν_mass_le_Mass n)
  set P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨p_meas n, hp_prob n⟩ with hP_def
  have h_tight : IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro η hη
    by_cases hη_top : η = ⊤
    · exact ⟨∅, isCompact_empty, fun _ _ => hη_top ▸ le_top⟩
    set δ := η.toReal with hδ_def
    have hδ_pos : 0 < δ := ENNReal.toReal_pos hη.ne' hη_top
    have hδ_le : ENNReal.ofReal δ ≤ η := by rw [hδ_def, ENNReal.ofReal_toReal hη_top]
    obtain ⟨R, hR1, hR⟩ := htail (δ/2) (by linarith)
    have hR_pos : 0 < R := lt_of_lt_of_le one_pos hR1
    refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
    intro μ' hμ'
    obtain ⟨ν', hν'_range, hν'_eq⟩ := hμ'
    obtain ⟨n, hPn⟩ := hν'_range
    rw [← hν'_eq, ← hPn]
    have hP_unfold : ((P n : ProbabilityMeasure ℝ) : Measure ℝ) = p_meas n := rfl
    rw [hP_unfold]
    have h0_in_K : (0 : ℝ) ∈ Set.Icc (-R) R := ⟨by linarith, by linarith⟩
    have hdirac0 : Measure.dirac 0 (Set.Icc (-R) R)ᶜ = 0 := by
      rw [Measure.dirac_apply' _ isClosed_Icc.measurableSet.compl, Set.indicator_apply]
      simp [h0_in_K]
    have hKc_sub : (Set.Icc (-R) R)ᶜ ⊆ largeSet R := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      change R ≤ |x|
      rcases hx with hx | hx
      · have h_neg : x < 0 := lt_of_lt_of_le hx (neg_nonpos_of_nonneg hR_pos.le)
        rw [abs_of_neg h_neg]; linarith
      · have h_pos : 0 < x := lt_of_le_of_lt hR_pos.le hx
        rw [abs_of_pos h_pos]; linarith
    have hν_n_Kc : ν n (Set.Icc (-R) R)ᶜ ≤ ENNReal.ofReal (δ/2) := by
      have h1 : ν n (Set.Icc (-R) R)ᶜ ≤ ν n (largeSet R) := measure_mono hKc_sub
      have h2 : ν n (largeSet R) ≤ ENNReal.ofReal (δ/2) := hR (t_seq n)
      exact h1.trans h2
    have hp_Kc : p_meas n (Set.Icc (-R) R)ᶜ ≤ ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal (δ/2) := by
      simp only [hp_meas_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hdirac0,
        mul_zero, add_zero]
      gcongr
    have hM_inv_le_one : Mass⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact hMass_ge_one
    have hM_inv_nn : (0 : ℝ) ≤ Mass⁻¹ := le_of_lt (inv_pos.mpr hMass_pos)
    have hfinal_real : Mass⁻¹ * (δ/2) ≤ δ := by
      calc Mass⁻¹ * (δ/2) ≤ 1 * (δ/2) :=
            mul_le_mul_of_nonneg_right hM_inv_le_one (by linarith)
        _ = δ/2 := one_mul _
        _ ≤ δ := by linarith
    have hfinal_ennreal : ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal (δ/2) ≤ ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_mul hM_inv_nn]; exact ENNReal.ofReal_le_ofReal hfinal_real
    calc p_meas n (Set.Icc (-R) R)ᶜ
        ≤ ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal (δ/2) := hp_Kc
      _ ≤ ENNReal.ofReal δ := hfinal_ennreal
      _ ≤ η := hδ_le
  have h_compact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet h_tight
  have h_in_range : ∀ n, P n ∈ closure (Set.range P) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨P_inf, _, φ, hφ_mono, hP_tendsto⟩ := h_compact.tendsto_subseq h_in_range
  let ν_out : Measure ℝ := (ENNReal.ofReal Mass) • (P_inf : Measure ℝ)
  have hν_out_fin : IsFiniteMeasure ν_out := by
    constructor
    simp only [ν_out, Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal Mass * (P_inf : Measure ℝ) Set.univ
        ≤ ENNReal.ofReal Mass * 1 := by gcongr; exact prob_le_one
      _ = ENNReal.ofReal Mass := by rw [mul_one]
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨ν_out, hν_out_fin, t_seq ∘ φ, ht_seq_tendsto.comp hφ_mono.tendsto_atTop, ?_⟩
  intro f hf0
  have hP_int := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP_tendsto) f
  simp only [Function.comp_apply, P, ProbabilityMeasure.coe_mk] at hP_int
  have h_int_ν_out : ∫ x, f x ∂ν_out = Mass * ∫ x, f x ∂(P_inf : Measure ℝ) := by
    show ∫ x, f x ∂((ENNReal.ofReal Mass) • (P_inf : Measure ℝ)) = Mass * _
    rw [integral_smul_measure, ENNReal.toReal_ofReal hMass_pos.le, smul_eq_mul]
  have h_int_P_eq : ∀ n, ∫ x, f x ∂(p_meas n) = Mass⁻¹ * ∫ x, f x ∂(ν n) := by
    intro n
    haveI : IsFiniteMeasure (ν n) := hν_finite n
    have h_integrable_ν : Integrable f (ν n) := f.integrable (ν n)
    have h_integrable_dirac : Integrable f (Measure.dirac (0 : ℝ)) :=
      integrable_dirac (by rw [hf0]; simp)
    have h_int1 : Integrable f (ENNReal.ofReal Mass⁻¹ • ν n) :=
      Integrable.smul_measure h_integrable_ν ENNReal.ofReal_ne_top
    have hcoeff_finite : ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν n Set.univ) ≠ ⊤ := by
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self
    have h_int2 : Integrable f ((ENNReal.ofReal Mass⁻¹ *
        (ENNReal.ofReal Mass - ν n Set.univ)) • Measure.dirac (0 : ℝ)) :=
      Integrable.smul_measure h_integrable_dirac hcoeff_finite
    show ∫ x, f x ∂(((ENNReal.ofReal Mass⁻¹) • ν n) +
        ((ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν n Set.univ)) •
          Measure.dirac (0 : ℝ))) = Mass⁻¹ * _
    rw [integral_add_measure h_int1 h_int2]
    rw [integral_smul_measure, integral_smul_measure, integral_dirac _ _]
    simp only [smul_eq_mul, hf0, mul_zero, add_zero]
    rw [show (ENNReal.ofReal Mass⁻¹).toReal = Mass⁻¹ from
      ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hMass_pos))]
  have h_int_ν_subseq : Tendsto (fun k => ∫ x, f x ∂(ν (φ k))) atTop
      (𝓝 (Mass * ∫ x, f x ∂(P_inf : Measure ℝ))) := by
    have hP_seq : Tendsto (fun k => ∫ x, f x ∂(p_meas (φ k))) atTop
        (𝓝 (∫ x, f x ∂(P_inf : Measure ℝ))) := hP_int
    have h_eq' : (fun k => ∫ x, f x ∂(p_meas (φ k))) =
        (fun k => Mass⁻¹ * ∫ x, f x ∂(ν (φ k))) := funext (fun k => h_int_P_eq (φ k))
    rw [h_eq'] at hP_seq
    have h_mul : Tendsto (fun k => Mass * (Mass⁻¹ * ∫ x, f x ∂(ν (φ k)))) atTop
        (𝓝 (Mass * ∫ x, f x ∂(P_inf : Measure ℝ))) := hP_seq.const_mul Mass
    refine h_mul.congr (fun k => ?_)
    rw [← mul_assoc, mul_inv_cancel₀ hMass_pos.ne', one_mul]
  show Tendsto (fun k => ∫ x, f x ∂(S.tiltedScaledMeasure (t_seq (φ k)))) atTop
    (𝓝 (∫ x, f x ∂ν_out))
  rw [h_int_ν_out]
  exact h_int_ν_subseq