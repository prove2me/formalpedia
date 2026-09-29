-- Prove2me | solution 1 for isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/721f9396-6956-511e-affa-5b3f11a913cd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow

set_option autoImplicit false

universe u

open Finset Polynomial

namespace StrongRootUnit

variable {R : Type u} [CommRing R]

theorem poly_eq_zero_of_degree_lt (n : ℕ) :
    ∀ (a : ℕ → R), (∀ i j : ℕ, i < n → j < n → i ≠ j → IsUnit (a i - a j)) →
      ∀ p : R[X], p.degree < n → (∀ i : ℕ, i < n → p.eval (a i) = 0) → p = 0 := by
  induction n with
  | zero =>
    intro a _ p hp _
    exact Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hp))
  | succ n ih =>
    intro a ha p hp hev
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    have hroot : p.IsRoot (a n) := hev n (Nat.lt_succ_self n)
    have hfac : (X - C (a n)) * (p /ₘ (X - C (a n))) = p := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
    set q := p /ₘ (X - C (a n)) with hq_def
    have hq0 : q = 0 := by
      apply ih a (fun i j hi hj hij => ha i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij) q
      · by_cases hq : q = 0
        · rw [hq, Polynomial.degree_zero]; exact WithBot.bot_lt_coe n
        · have hdeg : p.degree = q.degree + 1 := by
            rw [← hfac, mul_comm, Polynomial.Monic.degree_mul (Polynomial.monic_X_sub_C (a n)), Polynomial.degree_X_sub_C]
          rw [hdeg, Polynomial.degree_eq_natDegree hq] at hp
          rw [Polynomial.degree_eq_natDegree hq]
          have : q.natDegree + 1 < n + 1 := by exact_mod_cast hp
          exact_mod_cast Nat.lt_of_add_lt_add_right this
      · intro i hi
        have h := hev i (Nat.lt_succ_of_lt hi)
        rw [← hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
        exact ((ha i n (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self n) (Nat.ne_of_lt hi)).mul_right_eq_zero).mp h
    rw [← hfac, hq0, mul_zero]

theorem isUnit_pow_sub_pow {ζ : R} {m : ℕ} (hζ : ζ ^ m = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < m → IsUnit (1 - ζ ^ j)) {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    IsUnit (ζ ^ i - ζ ^ j) := by
  have hm : m ≠ 0 := by rintro rfl; exact absurd hi (Nat.not_lt_zero _)
  have hζU : IsUnit ζ := IsUnit.of_pow_eq_one hζ hm
  rcases lt_or_gt_of_ne hij with h | h
  · have : ζ ^ i - ζ ^ j = ζ ^ i * (1 - ζ ^ (j - i)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le]
    rw [this]
    exact (hζU.pow i).mul (hζu (j - i) (Nat.sub_pos_of_lt h) (lt_of_le_of_lt (Nat.sub_le j i) hj))
  · have : ζ ^ i - ζ ^ j = -(ζ ^ j * (1 - ζ ^ (i - j))) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le, neg_sub]
    rw [this]
    exact ((hζU.pow j).mul (hζu (i - j) (Nat.sub_pos_of_lt h) (lt_of_le_of_lt (Nat.sub_le i j) hi))).neg

theorem X_pow_sub_one_eq_prod {m : ℕ} (hm : 0 < m) {ζ : R} (hζ : ζ ^ m = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < m → IsUnit (1 - ζ ^ j)) :
    (X ^ m - 1 : R[X]) = ∏ j ∈ range m, (X - C (ζ ^ j)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hQm : (∏ j ∈ range m, (X - C (ζ ^ j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hQd : (∏ j ∈ range m, (X - C (ζ ^ j))).natDegree = m := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _]
    rw [Finset.sum_congr rfl (fun j _ => Polynomial.natDegree_X_sub_C (ζ ^ j)), Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  have hPm : (X ^ m - 1 : R[X]).Monic := by
    rw [← Polynomial.C_1]; exact Polynomial.monic_X_pow_sub_C _ hm.ne'
  have hPd : (X ^ m - 1 : R[X]).natDegree = m := by rw [← Polynomial.C_1]; exact Polynomial.natDegree_X_pow_sub_C
  rw [← sub_eq_zero]
  apply poly_eq_zero_of_degree_lt m (fun i => ζ ^ i) (fun i j hi hj hij => isUnit_pow_sub_pow hζ hζu hi hj hij)
  ·
    by_cases h0 : (X ^ m - 1 : R[X]) - ∏ j ∈ range m, (X - C (ζ ^ j)) = 0
    · rw [h0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe m
    · have := Polynomial.degree_sub_lt (p := (X ^ m - 1 : R[X])) (q := ∏ j ∈ range m, (X - C (ζ ^ j)))
        (by rw [Polynomial.degree_eq_natDegree hPm.ne_zero, Polynomial.degree_eq_natDegree hQm.ne_zero, hPd, hQd])
        hPm.ne_zero (by rw [hPm.leadingCoeff, hQm.leadingCoeff])
      rwa [Polynomial.degree_eq_natDegree hPm.ne_zero, hPd] at this
  · intro i hi
    rw [Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      ← pow_mul, mul_comm, pow_mul, hζ, one_pow, sub_self, Polynomial.eval_prod, zero_sub, neg_eq_zero]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

theorem main (N : ℕ) (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) :
    IsUnit ((N + 1 : ℕ) : R) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact isUnit_of_subsingleton _
  have hfac := X_pow_sub_one_eq_prod (Nat.succ_pos N) hζ hζu

  have hD := congrArg (fun p : R[X] => (Polynomial.derivative p).eval 1) hfac
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one, sub_zero,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, Polynomial.eval_C,
    Polynomial.derivative_prod_finset, Polynomial.eval_finset_sum, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C] at hD

  show IsUnit ((Nat.succ N : ℕ) : R)
  rw [hD, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos N))]
  · rw [Polynomial.eval_prod, IsUnit.prod_iff]
    intro j hj
    obtain ⟨hj0, hjm⟩ := Finset.mem_erase.mp hj
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact hζu j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hjm)
  · intro j hj hj0
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hj0, Finset.mem_range.mpr (Nat.succ_pos N)⟩)
    simp

end StrongRootUnit

theorem solution
    (R : Type u) [CommRing R] (N : ℕ) (ζ : R) (hζ : ζ ^ (N + 1) = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) :
    IsUnit ((N + 1 : ℕ) : R) :=
  StrongRootUnit.main N ζ hζ hζu

end S_isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow
end P2MW
export P2MW.S_isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow (solution)
