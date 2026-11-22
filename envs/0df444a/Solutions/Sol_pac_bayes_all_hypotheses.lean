-- Prove2me | solution 1 for pac_bayes_all_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:04.420884+00:00
-- url     : https://prove2.me/submissions/66671d2b-e565-410d-b748-f724bc646a36

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PACBayes
public import Theorems.Thm_pac_bayes_per_hypothesis
section
@[expose] public section
universe u
open MeasureTheory Finset
private lemma prob_ge_one_sub_compl' {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S : Set Ω) (δ : ENNReal)
    (h : μ Sᶜ ≤ δ) :
    μ S ≥ 1 - δ := by
  rw [ge_iff_le, tsub_le_iff_right]
  calc (1 : ENNReal)
      = μ Set.univ := (MeasureTheory.IsProbabilityMeasure.measure_univ).symm
    _ = μ (S ∪ Sᶜ) := by rw [Set.union_compl_self]
    _ ≤ μ S + μ Sᶜ := MeasureTheory.measure_union_le S Sᶜ
    _ ≤ μ S + δ := add_le_add_right h (μ S)
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Finset
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        ∀ h : H,
          TrueErrorReal X (hs h) c D ≤
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
            Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
      ≥ ENNReal.ofReal (1 - δ) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  set Good := { S : Fin m → X |
    ∀ h : H,
      TrueErrorReal X (hs h) c D ≤
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
  -- Goodᶜ ⊆ ⋃ h, {bad for h}
  have h_compl_sub : Goodᶜ ⊆ ⋃ h : H, { S : Fin m → X |
      TrueErrorReal X (hs h) c D >
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) } := by
    intro S hS
    simp only [Set.mem_compl_iff, Good, Set.mem_ofPred_eq, not_forall] at hS
    simp_all
  -- Per-hypothesis bounds
  have h_per : ∀ h : H, μ { S : Fin m → X |
      TrueErrorReal X (hs h) c D >
        EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
        Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
      ≤ ENNReal.ofReal (P.prob h * δ) := by
    intro h
    set t := Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m))
    by_cases ht1 : t ≤ 1
    · -- Normal case: t ≤ 1, apply per-hypothesis Hoeffding
      exact pac_bayes_per_hypothesis D c hc_meas hs hhs_meas P hP_pos m hm δ hδ hδ1 h ht1
    · -- t > 1 case: bad event is empty (gap ≤ 1 < t)
      push Not at ht1
      have h_empty : { S : Fin m → X |
          TrueErrorReal X (hs h) c D >
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i)))
              (zeroOneLoss Bool) + t } = ∅ := by
        ext S
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        -- TrueErrorReal ≤ 1 (probability measure)
        have h_true_le_one : TrueErrorReal X (hs h) c D ≤ 1 := by
          simp only [TrueErrorReal, TrueError]
          have h_le : D {x | hs h x ≠ c x} ≤ 1 := by
            calc D {x | hs h x ≠ c x} ≤ D Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
              _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
          exact ENNReal.toReal_le_of_le_ofReal one_pos.le
            (by rw [ENNReal.ofReal_one]; exact h_le)
        -- EmpiricalError ≥ 0
        have h_emp_nonneg : 0 ≤ EmpiricalError X Bool (hs h)
            (fun i => (S i, c (S i))) (zeroOneLoss Bool) := by
          simp only [EmpiricalError]
          split
          · exact le_refl 0
          · apply div_nonneg
            · apply Finset.sum_nonneg; intro i _
              simp only [zeroOneLoss]; split <;> linarith
            · positivity
        -- gap ≤ 1 ≤ 1 + emp ≤ emp + t (since t > 1 and emp ≥ 0)
        linarith
      simp_all
  -- Union bound + ∑ P(h)·δ = δ
  have h_compl_bound : μ Goodᶜ ≤ ENNReal.ofReal δ := by
    calc μ Goodᶜ
        ≤ μ (⋃ h : H, { S | TrueErrorReal X (hs h) c D >
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
            Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }) :=
          μ.mono h_compl_sub
      _ ≤ ∑ h : H, μ { S | TrueErrorReal X (hs h) c D >
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
            Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) } :=
          MeasureTheory.measure_iUnion_fintype_le μ _
      _ ≤ ∑ h : H, ENNReal.ofReal (P.prob h * δ) :=
          Finset.sum_le_sum (fun h _ => h_per h)
      _ ≤ ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_sum_of_nonneg
            (fun h _ => le_of_lt (mul_pos (hP_pos h) hδ)),
            ← Finset.sum_mul, P.prob_sum_one, one_mul]
  have h_result := prob_ge_one_sub_compl' μ Good (ENNReal.ofReal δ) h_compl_bound
  rw [ge_iff_le, ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]
  rwa [ge_iff_le] at h_result
