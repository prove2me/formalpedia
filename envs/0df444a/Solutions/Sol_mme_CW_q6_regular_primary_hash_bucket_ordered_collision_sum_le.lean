-- Prove2me | solution 1 for mme_CW_q6_regular_primary_hash_bucket_ordered_collision_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:30:20.797057+00:00
-- url     : https://prove2.me/submissions/e26d813c-d5dd-4bcb-b583-7e56a389c54e

import Mathlib
import Theorems.Thm_mme_CW_q6_literal_shared_xy_pair_parameter_card
import Theorems.Thm_mme_CW_q6_exact_subtype_collision_universe_card_le
import Theorems.Thm_mme_finite_incidence_first_second_moment_identities

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable local instance q6CollisionSumSolutionExactAddressDecidableEq
    (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) :=
  Classical.decEq _

noncomputable local instance q6CollisionSumSolutionCoupledAddressFintype
    (N : ℕ) : Fintype (CWQ6CoupledAddress N) :=
  inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))

noncomputable local instance q6CollisionSumSolutionExactAddressFintype
    (N L G : ℕ) : Fintype (CWQ6ExactCoupledAddress N L G) :=
  Fintype.ofInjective (fun e => e.1) Subtype.val_injective

/-- Sum the exact `|S|/M^3` survival count over the complete ordered X/Y
collision universe of a regular exact q=6 profile. -/
theorem solution
    {n L G : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) :
    let Xcount : ℕ := Nat.choose (n + 1) G
    let M : ℕ := 4 * Xcount ^ 2 + 1
    let Ω := (Fin (2 * n + 2) → ZMod M) × ZMod M
    (∑ ω : Ω,
      (let B := cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1
       ((B.product B).filter (fun p =>
        p.1 ≠ p.2 ∧
          (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))).card)) ≤
      2 *
        ((Nat.choose (2 * (n + 1)) L *
            Nat.choose (2 * (n + 1) - L) L) *
          Nat.choose (2 * G) G) *
        Xcount ^ 2 * S.card * M ^ (2 * n) := by
  classical
  let Xcount : ℕ := Nat.choose (n + 1) G
  let M : ℕ := 4 * Xcount ^ 2 + 1
  let Ω := (Fin (2 * n + 2) → ZMod M) × ZMod M
  let Eall : Finset (CWQ6ExactCoupledAddress (n + 1) L G) := Finset.univ
  let P := (Eall.product Eall).filter (fun p =>
    p.1 ≠ p.2 ∧
      (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))
  let Rel : Ω →
      (CWQ6ExactCoupledAddress (n + 1) L G ×
        CWQ6ExactCoupledAddress (n + 1) L G) → Prop := fun ω p =>
    p.1 ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1 ∧
    p.2 ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1
  have hfiber (ω : Ω) :
      (P.filter (Rel ω)).card =
        (let B := cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1
         ((B.product B).filter (fun p =>
          p.1 ≠ p.2 ∧
            (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))).card) := by
    let B := cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1
    congr 1
    ext p
    constructor
    · intro hp
      have hpF := Finset.mem_filter.mp hp
      have hpP := Finset.mem_filter.mp hpF.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr hpF.2, hpP.2⟩
    · intro hp
      have hpF := Finset.mem_filter.mp hp
      have hpB := Finset.mem_product.mp hpF.1
      apply Finset.mem_filter.mpr
      refine ⟨?_, hpB⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        hpF.2⟩
  have hinc :=
    (mme_finite_incidence_first_second_moment_identities
      (Finset.univ : Finset Ω) P Rel).1
  have hdouble :
      (∑ ω : Ω,
        (let B := cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1
         ((B.product B).filter (fun p =>
          p.1 ≠ p.2 ∧
            (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))).card)) =
        ∑ p ∈ P,
          ((Finset.univ : Finset Ω).filter (fun ω => Rel ω p)).card := by
    rw [← hinc]
    apply Finset.sum_congr rfl
    intro ω hω
    exact (hfiber ω).symm
  have hpairCard : ∀ p ∈ P,
      ((Finset.univ : Finset Ω).filter (fun ω => Rel ω p)).card =
        S.card * M ^ (2 * n) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hne := hp'.2.1
    have hshare := hp'.2.2
    simpa only [Ω, M, Xcount, Rel] using
      mme_CW_q6_literal_shared_xy_pair_parameter_card
        p.1 p.2 hne hshare S (by simpa [Xcount] using hSrange)
  have hsum :
      (∑ p ∈ P,
          ((Finset.univ : Finset Ω).filter (fun ω => Rel ω p)).card) =
        P.card * (S.card * M ^ (2 * n)) := by
    calc
      (∑ p ∈ P,
          ((Finset.univ : Finset Ω).filter (fun ω => Rel ω p)).card) =
          ∑ _p ∈ P, S.card * M ^ (2 * n) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpairCard p hp
      _ = P.card * (S.card * M ^ (2 * n)) := by simp
  have hPcard : P.card ≤
      2 *
        ((Nat.choose (2 * (n + 1)) L *
            Nat.choose (2 * (n + 1) - L) L) *
          Nat.choose (2 * G) G) *
        Xcount ^ 2 := by
    simp only [P, Eall, Xcount]
    exact
      mme_CW_q6_exact_subtype_collision_universe_card_le
        (n + 1) L G hregular
  dsimp only
  rw [hdouble, hsum]
  calc
    P.card * (S.card * M ^ (2 * n)) ≤
        (2 *
          ((Nat.choose (2 * (n + 1)) L *
              Nat.choose (2 * (n + 1) - L) L) *
            Nat.choose (2 * G) G) *
          Xcount ^ 2) * (S.card * M ^ (2 * n)) :=
      Nat.mul_le_mul_right _ hPcard
    _ = 2 *
        ((Nat.choose (2 * (n + 1)) L *
            Nat.choose (2 * (n + 1) - L) L) *
          Nat.choose (2 * G) G) *
        Xcount ^ 2 * S.card * M ^ (2 * n) := by ring
