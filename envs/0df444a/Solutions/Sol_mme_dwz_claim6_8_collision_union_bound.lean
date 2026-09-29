-- Prove2me | solution 1 for mme_dwz_claim6_8_collision_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:35:49.750657+00:00
-- url     : https://prove2.me/submissions/0b5b70b9-9cfd-4abc-b31d-22fead11f860

import Mathlib

open BigOperators

set_option autoImplicit false

/-!
The finite union-bound step underlying DWZ Claim 6.8.  A bad hash parameter
must collide with at least one compatible competitor.  If every competitor's
collision fiber has density at most `1 / M`, then the union of all bad fibers
has density at most the number of compatible competitors divided by `M`.
-/

theorem solution
    {Ω A : Type}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq A]
    (candidates : Finset A)
    (compatible : A → Prop) [DecidablePred compatible]
    (collides : A → Ω → Prop) [∀ a, DecidablePred (collides a)]
    (bad : Ω → Prop) [DecidablePred bad]
    (M : ℕ)
    (hbad : ∀ ω, bad ω →
      ∃ a ∈ candidates, compatible a ∧ collides a ω)
    (hcollision : ∀ a ∈ candidates, compatible a →
      M * (Finset.univ.filter (collides a)).card ≤ Fintype.card Ω) :
    M * (Finset.univ.filter bad).card ≤
      (candidates.filter compatible).card * Fintype.card Ω := by
  let C : Finset A := candidates.filter compatible
  let fiber : A → Finset Ω := fun a => Finset.univ.filter (collides a)
  have hsubset : Finset.univ.filter bad ⊆ C.biUnion fiber := by
    intro ω hω
    have hωbad : bad ω := (Finset.mem_filter.mp hω).2
    obtain ⟨a, ha, hac, haω⟩ := hbad ω hωbad
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨ha, hac⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ ω, haω⟩
  have hcard : (Finset.univ.filter bad).card ≤
      ∑ a ∈ C, (fiber a).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  calc
    M * (Finset.univ.filter bad).card ≤
        M * ∑ a ∈ C, (fiber a).card := Nat.mul_le_mul_left M hcard
    _ = ∑ a ∈ C, M * (fiber a).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _a ∈ C, Fintype.card Ω := by
      apply Finset.sum_le_sum
      intro a ha
      exact hcollision a (Finset.mem_filter.mp ha).1
        (Finset.mem_filter.mp ha).2
    _ = C.card * Fintype.card Ω := by simp
    _ = (candidates.filter compatible).card * Fintype.card Ω := rfl
