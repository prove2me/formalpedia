-- Prove2me | solution 1 for symmetrization_uc_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:50.520319+00:00
-- url     : https://prove2.me/submissions/16c2898a-19b8-400b-b785-d39aea940e67

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Theorems.Thm_symmetrization_step
public import Theorems.Thm_double_sample_pattern_bound
public import Theorems.Thm_symmetrization_step_lower

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
           (zeroOneLoss Bool)| ≥ ε}
    ≤ ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set gf_exp := (↑(GrowthFunction X C (2 * m)) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))
    with hgf_exp_def
  have hgf_exp_nn : 0 ≤ gf_exp := mul_nonneg (Nat.cast_nonneg' _) (Real.exp_pos _).le
  set upper := {xs : Fin m → X | ∃ h ∈ C, TrueErrorReal X h c D -
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
  have h_upper : μ upper ≤ ENNReal.ofReal (2 * gf_exp) := by
    have h1 := symmetrization_step D C c hmeas_C hc_meas m hm ε hε hm_large
    have h2 := double_sample_pattern_bound D C c hmeas_C hc_meas m hm ε hε hE_nullmeas
    calc μ upper ≤ 2 * (μ.prod μ) _ := h1
      _ ≤ 2 * ENNReal.ofReal gf_exp := by exact mul_le_mul_right h2 2
      _ = ENNReal.ofReal (2 * gf_exp) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  set lower := {xs : Fin m → X | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) -
      TrueErrorReal X h c D ≥ ε}
  have h_lower : μ lower ≤ ENNReal.ofReal (2 * gf_exp) := by
    have h1 := symmetrization_step_lower D C c hmeas_C hc_meas m hm ε hε hm_large
    have h_swap : (μ.prod μ)
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
      = (μ.prod μ)
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
      let swap_equiv : (Fin m → X) × (Fin m → X) ≃ᵐ (Fin m → X) × (Fin m → X) :=
        MeasurableEquiv.prodComm
      set S1 := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
      set S2 := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      have h_preimage : ⇑swap_equiv ⁻¹' S2 = S1 := by
        ext p
        change (p.2, p.1) ∈ S2 ↔ p ∈ S1
        simp only [S1, S2, Set.mem_ofPred_eq]
      have h_sym : (μ.prod μ).map swap_equiv = μ.prod μ :=
        (show (μ.prod μ).map ⇑swap_equiv = (μ.prod μ).map Prod.swap from rfl).trans
          (MeasureTheory.Measure.prod_swap (μ := μ) (ν := μ))
      calc (μ.prod μ) S1
          = (μ.prod μ) (⇑swap_equiv ⁻¹' S2) := by rw [h_preimage]
        _ = ((μ.prod μ).map swap_equiv) S2 := by rw [swap_equiv.map_apply]
        _ = (μ.prod μ) S2 := by rw [h_sym]
    have h2 := double_sample_pattern_bound D C c hmeas_C hc_meas m hm ε hε hE_nullmeas
    calc μ lower ≤ 2 * (μ.prod μ) _ := h1
      _ = 2 * (μ.prod μ) _ := by rw [h_swap]
      _ ≤ 2 * ENNReal.ofReal gf_exp := mul_le_mul_right h2 2
      _ = ENNReal.ofReal (2 * gf_exp) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have h_abs_sub : {xs : Fin m → X | ∃ h ∈ C,
      |TrueErrorReal X h c D -
       EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε}
      ⊆ upper ∪ lower := by
    intro xs ⟨h, hC, hgap⟩
    simp only [Set.mem_union]
    by_cases h_pos : TrueErrorReal X h c D -
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ 0
    · exact Or.inl ⟨h, hC, by rwa [abs_of_nonneg h_pos] at hgap⟩
    · push Not at h_pos
      have hgap' : -(TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)) ≥ ε := by
        rwa [abs_of_neg h_pos] at hgap
      exact Or.inr ⟨h, hC, by linarith⟩
  calc μ {xs | ∃ h ∈ C, |TrueErrorReal X h c D -
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε}
      ≤ μ (upper ∪ lower) := MeasureTheory.measure_mono h_abs_sub
    _ ≤ μ upper + μ lower := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * gf_exp) + ENNReal.ofReal (2 * gf_exp) :=
        add_le_add h_upper h_lower
    _ = ENNReal.ofReal (2 * gf_exp + 2 * gf_exp) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    _ = ENNReal.ofReal (4 * gf_exp) := by ring_nf
    _ = ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
          Real.exp (-(↑m * ε ^ 2 / 8))) := by rw [hgf_exp_def]; ring_nf
