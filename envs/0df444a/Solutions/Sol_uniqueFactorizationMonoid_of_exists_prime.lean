-- Prove2me | solution 1 for uniqueFactorizationMonoid_of_exists_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:20:21.718004+00:00
-- url     : https://prove2.me/submissions/a7e9067f-620a-4d61-83b6-c0509b610b9e

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
import Theorems.Thm_mem_kaplanskySet_iff_inter_eq_empty
import Theorems.Thm_span_ne_mem_kaplanskiSet

set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [CommSemiring R] [IsDomain R]
theorem _root_.solution
    (H : ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x) : UniqueFactorizationMonoid R := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun a ha ↦ ?_
  have ha₂ := span_ne_mem_kaplanskiSet ha H
  rw [mem_kaplanskySet_iff_inter_eq_empty] at ha₂
  rcases nonempty_iff_ne_empty.2 ha₂ with ⟨x, hx, hx₂⟩
  obtain ⟨b, hb⟩ := mem_span_singleton'.1 hx
  rw [← hb, mul_comm] at hx₂
  have hsubset : closure {r : R | Prime r} ≤ closure {r : R | IsUnit r ∨ Prime r} :=
    closure_mono (by grind)
  have := divisor_closure_eq_closure _ _ (hsubset hx₂)
  clear ha ha₂ hx hb hx₂
  induction this using closure_induction with
  | mem z hz =>
      rcases hz with h | h
      · exact ⟨∅, by simp, by simpa using (associated_one_iff_isUnit.2 h).symm⟩
      · exact ⟨{z}, by simpa, by simpa using Associated.rfl⟩
  | one => exact ⟨∅, by simp⟩
  | mul z₁ z₂ hz₁ hz₂ h₁ h₂ =>
      obtain ⟨S₁, hS₁pri, hS₁⟩ := h₁
      obtain ⟨S₂, hS₂pri, hS₂⟩ := h₂
      refine ⟨S₁ + S₂, by grind, ?_⟩
      rw [Multiset.prod_add]
      exact hS₁.mul_mul hS₂
