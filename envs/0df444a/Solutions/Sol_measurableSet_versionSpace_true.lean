-- Prove2me | solution 1 for measurableSet_versionSpace_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:53.502715+00:00
-- url     : https://prove2.me/submissions/f73cd27f-ce12-4eb8-a11b-db73f25dd60e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_VersionSpace
public import Theorems.Thm_measurableSet_isFirstConsistent
public import Theorems.Thm_nat_find_eq_iff_isFirstConsistent

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) :
    MeasurableSet ((fun p : (Fin m → X × Bool) × X =>
      (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {true}) := by
  classical
  -- Rewrite as countable union of rectangles
  have key : (fun p : (Fin m → X × Bool) × X =>
      (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {true}
      = ⋃ n, ({S : Fin m → X × Bool | IsFirstConsistent enum S n} ×ˢ
               {x : X | enum n x = true}) := by
    ext ⟨S, x⟩
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_prod, mem_ofPred_eq]
    constructor
    · intro hlearn
      show ∃ i, IsFirstConsistent enum S i ∧ enum i x = true
      change (if h : ∃ n, IsSampleConsistent (enum n) S then enum (Nat.find h)
            else fun _ => false) x = true at hlearn
      by_cases hex : ∃ n, IsSampleConsistent (enum n) S
      · simp only [dif_pos hex] at hlearn
        exact ⟨Nat.find hex, (nat_find_eq_iff_isFirstConsistent enum S hex _).mp rfl, hlearn⟩
      · rw [dif_neg hex] at hlearn; simp at hlearn
    · rintro ⟨n, hfirst, henum⟩
      change (if h : ∃ n, IsSampleConsistent (enum n) S then enum (Nat.find h)
            else fun _ => false) x = true
      have hex : ∃ k, IsSampleConsistent (enum k) S := ⟨n, hfirst.1⟩
      simp only [dif_pos hex]
      have heq : Nat.find hex = n :=
        (nat_find_eq_iff_isFirstConsistent enum S hex n).mpr hfirst
      rw [heq]; exact henum
  rw [key]
  exact .iUnion fun n =>
    (measurableSet_isFirstConsistent enum h_meas m n).prod
      ((h_meas n) (measurableSet_singleton true))
