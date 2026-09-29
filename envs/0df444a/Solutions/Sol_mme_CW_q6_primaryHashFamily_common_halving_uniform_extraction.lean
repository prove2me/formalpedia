-- Prove2me | solution 1 for mme_CW_q6_primaryHashFamily_common_halving_uniform_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:45:06.297179+00:00
-- url     : https://prove2.me/submissions/77cbfc70-3e0d-434e-ad20-a052097fadd9

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_primaryHashFamily_common_balanced_half_mass
import Theorems.Thm_mme_CW_q6_primaryHashFamily_uniform_subfamily
import Theorems.Thm_mme_CW_q6_primaryHashFamily_commonBalancedXYHalving_of_finset
import Theorems.Thm_mme_finite_fiber_threshold_polynomial

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

/-- A positive q=6 primary hash family has a common-halving uniform
subfamily, losing only the twentieth power of the length scale in its
cubic-square capacity. -/
theorem solution
    {n L G A H : ℕ} (hLG : L + G = 2 * n)
    (family : CWQ6PrimaryHashFamily (2 * n) L G A H)
    (hApos : 0 < A) (hHcap : H ≤ 4 ^ (2 * n)) :
    ∃ A' H' : ℕ,
      ∃ subfamily : CWQ6PrimaryHashFamily (2 * n) L G A' H',
        0 < A' ∧ 0 < H' ∧ H' ≤ 4 ^ (2 * n) ∧
        Nonempty subfamily.CommonBalancedXYHalving ∧
        A ^ 3 * H ^ 2 ≤
          128 * (2 * n + 1) ^ 20 * (A' ^ 3 * H' ^ 2) := by
  classical
  obtain ⟨S, P, hScard, hGoodP, hmass⟩ :=
    mme_CW_q6_primaryHashFamily_common_balanced_half_mass hLG family
  let Q : ℕ := (2 * n + 1) ^ 4
  let t : Fin A → ℕ := fun a ↦
    (P.filter (fun p ↦ p.1 = a)).card
  have ht (a : Fin A) : t a ≤ H := by
    have hsub : P.filter (fun p ↦ p.1 = a) ⊆
        ({a} : Finset (Fin A)).product Finset.univ := by
      intro p hp
      have heq := (Finset.mem_filter.mp hp).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr heq, Finset.mem_univ _⟩
    calc
      t a = (P.filter (fun p ↦ p.1 = a)).card := rfl
      _ ≤ (({a} : Finset (Fin A)).product
          (Finset.univ : Finset (Fin H))).card :=
        Finset.card_le_card hsub
      _ = H := by simp
  have hsum : (∑ a, t a) = P.card := by
    change (∑ a : Fin A, (P.filter (fun p ↦ p.1 = a)).card) = P.card
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  have hmass' : A * H ≤ Q * ∑ a, t a := by
    rw [hsum]
    exact hmass
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  obtain ⟨H', outer, hH'pos, hretained, hAbound, hHbound⟩ :=
    mme_finite_fiber_threshold_polynomial A H Q family.hHpos hQ t ht hmass'
  have houterPos : 0 < outer.card := by
    by_contra hzero
    have : outer.card = 0 := Nat.eq_zero_of_not_pos hzero
    rw [this] at hAbound
    simp only [Nat.mul_zero] at hAbound
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp houterPos
  have hH'le : H' ≤ H := (hretained a ha).trans (ht a)
  let Good : CWQ6ExactCoupledAddress (2 * n) L G → Prop :=
    fun address ↦
      (∀ grade : Fin 3,
        (S.filter (fun j ↦ address.1 0 j = grade)).card =
          if grade = 0 then n else if grade = 1 then n else 0) ∧
      (∀ grade : Fin 3,
        ((Finset.univ \ S).filter
          (fun j ↦ address.1 1 j = grade)).card =
          if grade = 0 then n else if grade = 1 then n else 0)
  obtain ⟨subfamily, hGoodSub, hH'le'⟩ :=
    mme_CW_q6_primaryHashFamily_uniform_subfamily family P outer Good
      hH'pos hH'le hretained (by
        intro p hp
        exact hGoodP p hp)
  have hhalving : Nonempty subfamily.CommonBalancedXYHalving :=
    mme_CW_q6_primaryHashFamily_commonBalancedXYHalving_of_finset
      subfamily S hScard
      (fun p grade ↦ (hGoodSub p).1 grade)
      (fun p grade ↦ (hGoodSub p).2 grade)
  refine ⟨outer.card, H', subfamily, houterPos, hH'pos,
    hH'le'.trans hHcap, hhalving, ?_⟩
  calc
    A ^ 3 * H ^ 2 ≤
        (2 * Q * outer.card) ^ 3 * (4 * Q * H') ^ 2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hAbound 3)
        (Nat.pow_le_pow_left hHbound 2)
    _ = 128 * (2 * n + 1) ^ 20 *
        (outer.card ^ 3 * H' ^ 2) := by
      dsimp [Q]
      ring
