-- Prove2me | solution 1 for empError_zero_iff_consistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:25.513055+00:00
-- url     : https://prove2.me/submissions/1f42da18-1e97-4e62-a9c0-df5cad24302a

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
theorem _root_.solution {X : Type u} {Y : Type v} [DecidableEq Y]
    (h : Concept X Y) {m : ℕ} (hm : 0 < m) (S : Fin m → X × Y)
    (loss : LossFunction Y) (hfaith : IsFaithfulLoss loss)
    (hloss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂) :
    EmpiricalError X Y h S loss = 0 ↔ IsConsistentWith X Y h S := by
  unfold EmpiricalError IsConsistentWith
  rw [if_neg (by omega : m ≠ 0)]
  constructor
  · -- EmpError = 0 → consistent
    intro hzero
    -- sum / m = 0 → sum = 0 (since m > 0)
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    rw [div_eq_zero_iff] at hzero
    cases hzero with
    | inl hsum =>
      -- sum = 0 and each term ≥ 0 → each term = 0
      have hterms := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hloss_nonneg _ _) |>.mp hsum
      intro i
      exact hfaith.loss_zero_imp_eq _ _ (hterms i (Finset.mem_univ i))
    | inr hm_zero => linarith
  · -- consistent → EmpError = 0
    intro hcons
    have : (Finset.univ.sum fun i : Fin m =>
        loss (h (S i).1) (S i).2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hcons i]
      exact hfaith.loss_self_zero _
    rw [this, zero_div]
