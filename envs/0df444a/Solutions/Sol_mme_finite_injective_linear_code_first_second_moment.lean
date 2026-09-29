-- Prove2me | solution 1 for mme_finite_injective_linear_code_first_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:30:59.01067+00:00
-- url     : https://prove2.me/submissions/7632612d-d318-43c3-a8ac-15702daf0a15

import Theorems.Thm_mme_ZMod_unit_linear_hash_fiber_card
import Theorems.Thm_mme_ZMod_two_linear_hash_fiber_card
import Theorems.Thm_mme_finset_equal_or_opposite_code_pairs_card_le
import Theorems.Thm_mme_finite_incidence_first_second_moment_identities

open BigOperators

set_option autoImplicit false

/-- Exact first moment and a dependency-aware second-moment bound for a
finite injective family of linear codes. -/
theorem solution
    {M n : ℕ} {α : Type} [NeZero M] [DecidableEq α]
    (A : Finset α)
    (c : α → Fin (n + 2) → ZMod M)
    (hunit : ∀ a ∈ A, ∃ j, IsUnit (c a j))
    (hinj : Function.Injective c)
    (hminor : ∀ a ∈ A, ∀ b ∈ A,
      c a ≠ c b → c a ≠ (fun i => -c b i) →
      ∃ j k, IsUnit (c a j * c b k - c a k * c b j)) :
    (∑ w : Fin (n + 2) → ZMod M,
        (A.filter (fun a => ∑ i, c a i * w i = 0)).card) =
          A.card * M ^ (n + 1) ∧
    (∑ w : Fin (n + 2) → ZMod M,
        (A.filter (fun a => ∑ i, c a i * w i = 0)).card ^ 2) ≤
          2 * A.card * M ^ (n + 1) + A.card ^ 2 * M ^ n := by
  classical
  let P : (Fin (n + 2) → ZMod M) → α → Prop :=
    fun w a => ∑ i, c a i * w i = 0
  let Dep : α × α → Prop := fun p =>
    c p.1 = c p.2 ∨ c p.1 = (fun i => -c p.2 i)
  have hmom := mme_finite_incidence_first_second_moment_identities
    (Finset.univ : Finset (Fin (n + 2) → ZMod M)) A P
  have hsingle : ∀ a ∈ A,
      ((Finset.univ.filter (fun w : Fin (n + 2) → ZMod M => P w a)).card) =
        M ^ (n + 1) := by
    intro a ha
    obtain ⟨j, hj⟩ := hunit a ha
    simpa only [P] using mme_ZMod_unit_linear_hash_fiber_card
      (M := M) (n := n + 1) (c a) j hj 0
  constructor
  · rw [hmom.1]
    calc
      ∑ a ∈ A,
          (Finset.univ.filter (fun w : Fin (n + 2) → ZMod M => P w a)).card =
          ∑ _a ∈ A, M ^ (n + 1) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hsingle a ha
      _ = A.card * M ^ (n + 1) := by simp
  · rw [hmom.2]
    have hpairBound : ∀ p ∈ A.product A,
        (Finset.univ.filter (fun w : Fin (n + 2) → ZMod M =>
          P w p.1 ∧ P w p.2)).card ≤
          M ^ n + if Dep p then M ^ (n + 1) else 0 := by
      intro p hp
      have hpA := Finset.mem_product.mp hp
      by_cases hdep : Dep p
      · have hsubset :
            Finset.univ.filter (fun w : Fin (n + 2) → ZMod M =>
                P w p.1 ∧ P w p.2) ⊆
              Finset.univ.filter (fun w : Fin (n + 2) → ZMod M => P w p.1) := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.1⟩
        have hcard := Finset.card_le_card hsubset
        rw [hsingle p.1 hpA.1] at hcard
        simp only [hdep, if_true]
        omega
      · have hne : c p.1 ≠ c p.2 := by
          intro heq
          exact hdep (Or.inl heq)
        have hnneg : c p.1 ≠ (fun i => -c p.2 i) := by
          intro heq
          exact hdep (Or.inr heq)
        obtain ⟨j, k, hjk⟩ := hminor p.1 hpA.1 p.2 hpA.2 hne hnneg
        have hexact := mme_ZMod_two_linear_hash_fiber_card (M := M) (n := n)
          (c p.1) (c p.2) j k hjk 0 0
        simp only [P, hdep, if_false, add_zero]
        exact le_of_eq hexact
    calc
      ∑ p ∈ A.product A,
          (Finset.univ.filter (fun w : Fin (n + 2) → ZMod M =>
            P w p.1 ∧ P w p.2)).card ≤
          ∑ p ∈ A.product A,
            (M ^ n + if Dep p then M ^ (n + 1) else 0) := by
              exact Finset.sum_le_sum hpairBound
      _ = (A.product A).card * M ^ n +
          ((A.product A).filter Dep).card * M ^ (n + 1) := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Nat.nsmul_eq_mul]
            have hindicator :
                (∑ p ∈ A.product A,
                  if Dep p then M ^ (n + 1) else 0) =
                  ((A.product A).filter Dep).card * M ^ (n + 1) := by
              rw [← Finset.sum_filter]
              simp
            rw [hindicator]
      _ ≤ A.card ^ 2 * M ^ n + (2 * A.card) * M ^ (n + 1) := by
            apply Nat.add_le_add
            · simp [pow_two]
            · apply Nat.mul_le_mul_right
              exact mme_finset_equal_or_opposite_code_pairs_card_le A c hinj
      _ = 2 * A.card * M ^ (n + 1) + A.card ^ 2 * M ^ n := by omega
