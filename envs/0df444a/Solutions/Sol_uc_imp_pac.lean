-- Prove2me | solution 1 for uc_imp_pac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:46.408948+00:00
-- url     : https://prove2.me/submissions/1c464b92-6f62-4e09-8d63-3eaf5cede1f4

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : C.Nonempty)
    (hUC : HasUniformConvergence X C) :
    PACLearnable X C := by
  classical
  -- Step 1: Construct a consistent learner (picks any h ∈ C agreeing with sample)
  -- Helper: the learning function
  let learnFn : {m : ℕ} → (Fin m → X × Bool) → Concept X Bool := fun {m} S =>
    if h : ∃ h₀ ∈ C, ∀ i : Fin m, h₀ (S i).1 = (S i).2
    then h.choose
    else hC.some
  have learn_in_H : ∀ {m : ℕ} (S : Fin m → X × Bool), learnFn S ∈ C := by
    intro m S
    change (if h : ∃ h₀ ∈ C, ∀ i : Fin m, h₀ (S i).1 = (S i).2
          then h.choose else hC.some) ∈ C
    split
    · next h => exact h.choose_spec.1
    · exact hC.some_mem
  let L : BatchLearner X Bool := {
    hypotheses := C
    learn := learnFn
    output_in_H := learn_in_H
  }
  -- Step 2: Extract sample complexity from UC
  -- PACLearnable needs: ∃ L mf, ∀ ε δ > 0, ...
  -- UC gives: ∀ ε δ > 0, ∃ m₀, ...
  -- We need mf ε δ chosen BEFORE ε, δ are universally quantified in the goal.
  -- Use UC to define mf: for ε > 0, δ > 0, pick m₀. For non-positive, pick 0.
  let mf : ℝ → ℝ → ℕ := fun ε δ =>
    if hε : 0 < ε then
      if hδ : 0 < δ then (hUC ε δ hε hδ).choose
      else 0
    else 0
  refine ⟨L, mf, ?_⟩
  intro ε δ hε hδ D hD c hcC
  -- Unfold mf to get the UC m₀
  have hmf : mf ε δ = (hUC ε δ hε hδ).choose := by
    simp only [mf, dif_pos hε, dif_pos hδ]
  -- Get the UC guarantee at m = mf ε δ
  set m := mf ε δ with hm_def
  have hUC_spec := (hUC ε δ hε hδ).choose_spec
  -- hUC_spec : ∀ D, IsProbabilityMeasure D → ∀ c, ∀ m', choose ≤ m' → ...
  have hUC_inst := hUC_spec D hD c m (by rw [hmf])
  -- Step 3: Show UC event ⊆ PAC event, then use measure monotonicity
  -- Goal: Measure.pi {PAC set} ≥ ofReal (1 - δ)
  -- i.e., ofReal (1-δ) ≤ Measure.pi {PAC set}
  -- We have: ofReal (1-δ) ≤ Measure.pi {UC set} (from hUC_inst)
  -- We show: {UC set} ⊆ {PAC set}, hence Measure.pi {UC set} ≤ Measure.pi {PAC set}
  apply ge_trans _ hUC_inst
  -- Now goal: Measure.pi {PAC set} ≥ Measure.pi {UC set}
  apply MeasureTheory.OuterMeasure.mono
  intro xs hxs
  simp only [Set.mem_ofPred_eq] at hxs ⊢
  -- The learner's output on the labeled sample
  set S := (fun i => (xs i, c (xs i)) : Fin m → X × Bool) with hS_def
  set h₀ := L.learn S with hh₀_def
  -- h₀ ∈ C (by output_in_H)
  have hh₀C : h₀ ∈ C := L.output_in_H S
  -- h₀ is consistent with the sample (since c ∈ C, the ∃ branch fires)
  have hcons : IsConsistentWith X Bool h₀ S := by
    -- learnFn S takes the dif_pos branch because c witnesses the existential
    have hexists : ∃ h₁ ∈ C, ∀ i : Fin m, h₁ ((fun i => (xs i, c (xs i))) i).1 =
        ((fun i => (xs i, c (xs i))) i).2 := ⟨c, hcC, fun i => rfl⟩
    unfold IsConsistentWith
    intro i
    change learnFn S (S i).1 = (S i).2
    simp only [learnFn, hS_def, dif_pos hexists]
    exact (hexists.choose_spec).2 i
  -- Bridge from consistency to TrueError ≤ ENNReal.ofReal ε
  -- First get UC bound for h₀
  have hxs_h₀ := hxs h₀ hh₀C
  -- Show EmpiricalError = 0 (handles both m = 0 and m > 0 cases)
  have hempzero : EmpiricalError X Bool h₀ S (zeroOneLoss Bool) = 0 := by
    unfold EmpiricalError
    by_cases hm0 : m = 0
    · simp [hm0]
    · rw [if_neg hm0]
      have : (Finset.univ.sum fun i : Fin m =>
          zeroOneLoss Bool (h₀ (S i).1) (S i).2) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        unfold zeroOneLoss
        rw [if_pos (hcons i)]
      rw [this, zero_div]
  rw [hempzero, sub_zero] at hxs_h₀
  -- |TrueErrorReal| < ε, and TrueErrorReal ≥ 0
  have hte_nonneg : 0 ≤ TrueErrorReal X h₀ c D := ENNReal.toReal_nonneg
  rw [abs_of_nonneg hte_nonneg] at hxs_h₀
  -- TrueErrorReal < ε means (D {x | h₀ x ≠ c x}).toReal < ε
  unfold TrueErrorReal TrueError at hxs_h₀
  -- D {x | h₀ x ≠ c x} ≠ ⊤ (probability measure → finite measure)
  have hne_top : D {x | h₀ x ≠ c x} ≠ ⊤ := MeasureTheory.measure_ne_top D _
  -- Convert: (D S).toReal < ε → D S < ENNReal.ofReal ε → D S ≤ ENNReal.ofReal ε
  have hlt : D {x | h₀ x ≠ c x} < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hne_top]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hxs_h₀
  exact le_of_lt hlt
