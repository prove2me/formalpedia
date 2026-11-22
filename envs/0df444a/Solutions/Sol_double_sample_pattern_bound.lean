-- Prove2me | solution 1 for double_sample_pattern_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:48.122073+00:00
-- url     : https://prove2.me/submissions/67666af1-1ea3-488e-8a5b-3369f1ffe5ec

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Theorems.Thm_exchangeability_chain_bound
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
theorem _root_.solution {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
      (MeasureTheory.Measure.pi (fun _ : Fin m => D))
    {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set bound := (↑(GrowthFunction X C (2 * m)) : ℝ) *
    Real.exp (-(↑m * ε ^ 2 / 8)) with hbound_def
  have hbound_nonneg : 0 ≤ bound := mul_nonneg (Nat.cast_nonneg' _) (Real.exp_pos _).le
  set E := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
    EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
    EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i)))
      (zeroOneLoss Bool) ≥ ε / 2} with hE_def
  by_cases hC : C = ∅
  · -- Event is empty when C is empty
    have hE_empty : E = ∅ := by
      ext p; simp only [hE_def, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨h_hyp, h_in_C, _⟩
      rw [hC] at h_in_C; exact h_in_C
    rw [hE_empty, MeasureTheory.measure_empty]; exact bot_le
  · -- C is nonempty
    by_cases hε2 : 2 < ε
    · -- EmpiricalError ∈ [0,1], so gap ∈ [-1,1] and ε/2 > 1 makes event empty
      have hE_empty : E = ∅ := by
        ext p; simp only [hE_def, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro ⟨h_hyp, h_in_C, h_gap⟩
        have h_emp_le := empiricalError_zeroOne_le_one h_hyp hm (fun i => (p.2 i, c (p.2 i)))
        have h_emp_nn := empiricalError_zeroOne_nonneg h_hyp hm (fun i => (p.1 i, c (p.1 i)))
        linarith
      rw [hE_empty, MeasureTheory.measure_empty]; exact bot_le
    · -- ε ≤ 2
      push Not at hε2
      by_cases h_triv : 1 ≤ bound
      · have : MeasureTheory.IsProbabilityMeasure (μ.prod μ) := by
          rw [hμ_def]
          infer_instance
        calc (μ.prod μ) E
            ≤ (μ.prod μ) Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
          _ = 1 := MeasureTheory.measure_univ
          _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal h_triv
      · -- Case 4: C ≠ ∅, ε ∈ (0, 2], bound < 1
        push Not at h_triv
        set μ_sum := MeasureTheory.Measure.pi
          (fun _ : Fin m ⊕ Fin m => D)
        set φ := MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Fin m ⊕ Fin m => X)
        have h_mp : MeasureTheory.MeasurePreserving φ μ_sum (μ.prod μ) := by
          change MeasureTheory.MeasurePreserving
            (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => X))
            (MeasureTheory.Measure.pi (fun _ : Fin m ⊕ Fin m => D))
            ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
              (MeasureTheory.Measure.pi (fun _ : Fin m => D)))
          exact MeasureTheory.measurePreserving_sumPiEquivProdPi
            (fun _ : Fin m ⊕ Fin m => D)
        exact exchangeability_chain_bound D C c hmeas_C hc_meas m hm ε hε hε2
          (Set.nonempty_iff_ne_empty.mpr hC) hE_nullmeas
