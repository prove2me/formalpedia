-- Prove2me | solution 1 for erm_consistent_realizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:24.231821+00:00
-- url     : https://prove2.me/submissions/e61f03ef-7320-4a39-b678-6bfd64cef1fd

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Theorems.Thm_empError_zero_iff_consistent

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [DecidableEq Bool]
    (H : HypothesisSpace X Bool) (C : ConceptClass X Bool)
    (loss : LossFunction Bool) (hfaith : IsFaithfulLoss loss)
    (hloss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂)
    (hne : H.Nonempty)
    (hreal : C ⊆ H) (c : Concept X Bool) (hcC : c ∈ C)
    {m : ℕ} (S : Fin m → X) :
    IsConsistentWith X Bool (ermLearn X Bool H loss hne (fun i => (S i, c (S i))))
      (fun i => (S i, c (S i))) := by
  -- Proof: c ∈ C ⊆ H has EmpError = 0 (by faithful loss, each loss(c(xᵢ), c(xᵢ)) = 0).
  -- Since loss is nonneg, EmpError ≥ 0 for all h. So c is a minimizer of EmpError over H.
  -- Therefore the ∃-condition in ermLearn fires (dif_pos), and the ERM output h₀ satisfies
  -- EmpError(h₀) ≤ EmpError(c) = 0, hence EmpError(h₀) = 0, hence h₀ is consistent.
  set S' := (fun i => (S i, c (S i))) with hS'_def
  -- Step 1: EmpiricalError of c on S' is 0 (faithful loss: loss(y,y) = 0)
  have hc_emp_zero : EmpiricalError X Bool c S' loss = 0 := by
    unfold EmpiricalError
    by_cases hm : m = 0
    · rw [if_pos hm]
    · rw [if_neg hm]
      have hsum : (Finset.univ.sum fun i : Fin m =>
          loss (c (S' i).1) (S' i).2) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [hS'_def]
        exact hfaith.loss_self_zero _
      rw [hsum, zero_div]
  -- Step 2: EmpiricalError is nonneg for any h (since loss is nonneg)
  have hEmp_nonneg : ∀ h' : Concept X Bool, 0 ≤ EmpiricalError X Bool h' S' loss := by
    intro h'
    unfold EmpiricalError
    by_cases hm : m = 0
    · rw [if_pos hm]
    · rw [if_neg hm]
      apply div_nonneg
      · exact Finset.sum_nonneg (fun i _ => hloss_nonneg _ _)
      · exact Nat.cast_nonneg (α := ℝ) m
  -- Step 3: c is a minimizer, so the ∃-condition in ermLearn holds
  have hexists : ∃ h₀ ∈ H, ∀ h' ∈ H,
      EmpiricalError X Bool h₀ S' loss ≤ EmpiricalError X Bool h' S' loss := by
    refine ⟨c, hreal hcC, fun h' _ => ?_⟩
    simp_all
  -- Step 4: Unfold ermLearn, the if branch fires
  unfold ermLearn
  rw [dif_pos hexists]
  -- Step 5: The chosen minimizer h₀ has EmpError(h₀) ≤ EmpError(c) = 0
  obtain ⟨hch_mem, hch_min⟩ := hexists.choose_spec
  have hch_le : EmpiricalError X Bool hexists.choose S' loss ≤ 0 := by
    have := hch_min c (hreal hcC)
    rwa [hc_emp_zero] at this
  -- Step 6: EmpError(h₀) = 0 (since 0 ≤ EmpError ≤ 0)
  have hch_zero : EmpiricalError X Bool hexists.choose S' loss = 0 :=
    le_antisymm hch_le (hEmp_nonneg _)
  -- Step 7: By empError_zero_iff_consistent, h₀ is consistent
  by_cases hm : (0 : ℕ) < m
  · exact (empError_zero_iff_consistent hexists.choose hm S' loss hfaith hloss_nonneg).mp hch_zero
  · -- m = 0: IsConsistentWith is vacuously true (no samples)
    push Not at hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst hm0
    intro i; exact i.elim0
