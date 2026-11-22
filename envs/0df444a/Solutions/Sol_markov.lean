-- Prove2me | solution 1 for markov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:39.026272+00:00
-- url     : https://prove2.me/submissions/e92c2d5c-3bfe-4a33-aef1-17ac83e7cd14

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_Polychromatic_DiscreteProbability

set_option autoImplicit true
open Finset
variable {ι α : Type*} {s : Finset ι} {p f : ι → α} {c : α} [LinearOrder α]
theorem _root_.solution [DivisionSemiring α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hf : ∀ i ∈ s, 0 ≤ f i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ f i, p i ≤ (∑ i ∈ s, p i * f i) / c := by
  rw [le_div_iff₀ hc]
  calc
    (∑ i ∈ s with c ≤ f i, p i) * c = ∑ i ∈ s with c ≤ f i, p i * c := by rw [sum_mul]
    _ ≤ ∑ i ∈ s with c ≤ f i, p i * f i := sum_le_sum fun i hi ↦ by
      simp only [mem_filter] at hi
      exact mul_le_mul_of_nonneg_left hi.2 (hp _ hi.1)
    _ ≤ ∑ i ∈ s, p i * f i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun i hi _ ↦ mul_nonneg (hp i hi) (hf i hi)
