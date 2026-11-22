-- Prove2me | solution 1 for symmetrization_step_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:20.473612+00:00
-- url     : https://prove2.me/submissions/352d2180-48fd-49d0-b9a7-51ab3cbc73e2

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Theorems.Thm_hoeffding_one_sided_upper
section
@[expose] public section
universe u v
open MeasureTheory ENNReal
private theorem empiricalError_zeroOne_nonneg {X : Type u} (h : Concept X Bool) {m : ℕ}
    (hm : 0 < m) (S : Fin m → X × Bool) :
    0 ≤ EmpiricalError X Bool h S (zeroOneLoss Bool) := by
  simp only [EmpiricalError, Nat.pos_iff_ne_zero.mp hm, ↓reduceIte]
  exact div_nonneg (Finset.sum_nonneg fun i _ => by
    simp only [zeroOneLoss]; split <;> linarith) (Nat.cast_nonneg' m)
private theorem empiricalError_zeroOne_le_one {X : Type u} (h : Concept X Bool) {m : ℕ}
    (hm : 0 < m) (S : Fin m → X × Bool) :
    EmpiricalError X Bool h S (zeroOneLoss Bool) ≤ 1 := by
  simp only [EmpiricalError, Nat.pos_iff_ne_zero.mp hm, ↓reduceIte]
  rw [div_le_one (Nat.cast_pos.mpr hm)]
  exact (Finset.sum_le_card_nsmul Finset.univ _ 1 fun i _ => by
    simp only [zeroOneLoss]; split <;> linarith).trans (by simp)
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C, EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) - TrueErrorReal X h c D ≥ ε}
    ≤ 2 * (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
        (MeasureTheory.Measure.pi (fun _ : Fin m => D))
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set A := {xs : Fin m → X | ∃ h ∈ C, EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
      (zeroOneLoss Bool) - TrueErrorReal X h c D ≥ ε}
    with hA_def
  set B := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hB_def
  suffices h_half : (1 : ℝ≥0∞) / 2 * μ A ≤ (μ.prod μ) B by
    have h2 : μ A ≤ 2 * ((1 : ℝ≥0∞) / 2 * μ A) := by
      rw [← mul_assoc, show (2 : ℝ≥0∞) * (1 / 2) = 1 from by
        simp [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by exact ENNReal.ofNat_ne_top)]]
      simp
    exact h2.trans (mul_le_mul_right h_half 2)
  set B' := MeasureTheory.toMeasurable (μ.prod μ) B with hB'_def
  have hB'_meas : MeasurableSet B' := MeasureTheory.measurableSet_toMeasurable _ _
  set f : (Fin m → X) → ℝ≥0∞ := fun xs => μ (Prod.mk xs ⁻¹' B') with hf_def
  have hf_meas : Measurable f := measurable_measure_prodMk_left hB'_meas
  have h_cond : ∀ xs ∈ A, (1 : ℝ≥0∞) / 2 ≤ f xs := by
    intro xs hxs
    obtain ⟨h_star, h_star_in_C, h_gap⟩ := hxs
    set S_ghost := {xs' : Fin m → X | EmpiricalError X Bool h_star
        (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h_star
        (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) ≥ ε / 2} with hS_ghost_def
    have h_ghost_sub_B : S_ghost ⊆ Prod.mk xs ⁻¹' B := by
      intro xs' hxs'
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hB_def]
      exact ⟨h_star, h_star_in_C, hxs'⟩
    have h_B_sub_B' : Prod.mk xs ⁻¹' B ⊆ Prod.mk xs ⁻¹' B' :=
      Set.preimage_mono (MeasureTheory.subset_toMeasurable _ _)
    calc (1 : ℝ≥0∞) / 2
        ≤ μ S_ghost := by
          have hmeas_disagree : MeasurableSet {x | h_star x ≠ c x} :=
            (measurableSet_eq_fun (hmeas_C h_star h_star_in_C) hc_meas).compl
          have h_emp_nonneg := empiricalError_zeroOne_nonneg h_star hm (fun i => (xs i, c (xs i)))
          have h_true_le_one : TrueErrorReal X h_star c D ≤ 1 := measureReal_le_one
          have h_true_nonneg : (0 : ℝ) ≤ TrueErrorReal X h_star c D := by
            simp only [TrueErrorReal, TrueError]
            positivity
          have h_emp_le_one := empiricalError_zeroOne_le_one h_star hm (fun i => (xs i, c (xs i)))
          by_cases hε1 : ε ≤ 1
          case neg =>
            push Not at hε1
            linarith
          case pos =>
          have hε2_pos : (0 : ℝ) < ε / 2 := by linarith
          have hε2_le_one : ε / 2 ≤ 1 := by linarith
          have h_hoeff := hoeffding_one_sided_upper D h_star c m hm (ε / 2) hε2_pos hε2_le_one
            hmeas_disagree
          have h_exp_le_half : Real.exp (-2 * ↑m * (ε / 2) ^ 2) ≤ 1 / 2 := by
            rw [show -2 * ↑m * (ε / 2) ^ 2 = -(↑m * ε ^ 2 / 2) from by ring,
                Real.exp_neg, show (1 : ℝ) / 2 = 2⁻¹ from by norm_num]
            apply inv_anti₀ (by positivity)
            calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
              _ ≤ Real.exp (↑m * ε ^ 2 / 2) := Real.exp_le_exp_of_le (by linarith)
          set H_set := {xs' : Fin m → X | EmpiricalError X Bool h_star
              (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) ≥
              TrueErrorReal X h_star c D + ε / 2} with hH_set_def
          have h_H_le_half : μ H_set ≤ 1 / 2 :=
            h_hoeff.trans (ENNReal.ofReal_le_ofReal h_exp_le_half |>.trans (by
              rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
              simp [ENNReal.ofReal_one]))
          have h_compl_ge : 1 / 2 ≤ μ H_setᶜ := by
            have h_total : 1 ≤ μ H_set + μ H_setᶜ := by
              have := measure_union_le (μ := μ) H_set H_setᶜ
              rwa [Set.union_compl_self, measure_univ] at this
            have h_H_ne_top : μ H_set ≠ ⊤ :=
              ne_top_of_le_ne_top ENNReal.one_ne_top (h_H_le_half.trans (by norm_num))
            calc (1 : ℝ≥0∞) / 2
                = 1 - 1 / 2 := by norm_num
              _ ≤ 1 - μ H_set := tsub_le_tsub_left h_H_le_half 1
              _ ≤ (μ H_set + μ H_setᶜ) - μ H_set := tsub_le_tsub_right h_total (μ H_set)
              _ = μ H_setᶜ := ENNReal.add_sub_cancel_left h_H_ne_top
          have h_compl_sub : H_setᶜ ⊆ S_ghost := by
            intro xs' hxs'
            simp only [Set.mem_compl_iff, hH_set_def, Set.mem_ofPred_eq, not_le] at hxs'
            simp only [hS_ghost_def, Set.mem_ofPred_eq, ge_iff_le]
            linarith
          exact h_compl_ge.trans (MeasureTheory.measure_mono h_compl_sub)
      _ ≤ μ (Prod.mk xs ⁻¹' B') :=
          MeasureTheory.measure_mono (h_ghost_sub_B.trans h_B_sub_B')
  have h_markov : (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} ≤ ∫⁻ xs, f xs ∂μ :=
    mul_meas_ge_le_lintegral hf_meas _
  have h_prod : (μ.prod μ) B' = ∫⁻ xs, μ (Prod.mk xs ⁻¹' B') ∂μ :=
    MeasureTheory.Measure.prod_apply hB'_meas
  calc (1 : ℝ≥0∞) / 2 * μ A
      ≤ (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} := by
        apply mul_le_mul_right
        exact MeasureTheory.measure_mono h_cond
    _ ≤ ∫⁻ xs, f xs ∂μ := h_markov
    _ = (μ.prod μ) B' := h_prod.symm
    _ = (μ.prod μ) B := MeasureTheory.measure_toMeasurable B
