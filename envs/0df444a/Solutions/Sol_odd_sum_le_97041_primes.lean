-- Prove2me | solution 1 for odd_sum_le_97041_primes
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T04:06:15.903286+00:00
-- url     : https://prove2.me/submissions/9a2381c9-0101-4484-8382-2cdde56a81fd

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_density_A
import Theorems.Thm_Schnir_schnirelmann_ineq

open Finset Real

namespace Schnir

open Pointwise

/-- Iterated sumsets `iter k = k A` (with `iter 0 = {0}`). -/
def main_iter : ℕ → Set ℕ
  | 0 => {0}
  | k + 1 => main_iter k + A

theorem main_zero_mem_A : (0 : ℕ) ∈ A :=
  Set.mem_add.2 ⟨0, ⟨3, Nat.prime_three, by norm_num, rfl⟩, 0, ⟨3, Nat.prime_three, by norm_num, rfl⟩,
    rfl⟩

theorem main_zero_mem_iter (k : ℕ) : 0 ∈ main_iter k := by
  induction k with
  | zero => rfl
  | succ k ih => exact Set.mem_add.2 ⟨0, ih, 0, main_zero_mem_A, rfl⟩

open Classical in
theorem main_density_iter (k : ℕ) :
    1 - (1 - schnirelmannDensity A) ^ k ≤ schnirelmannDensity (main_iter k) := by
  induction k with
  | zero => simp [schnirelmannDensity_nonneg]
  | succ k ih =>
    have h := schnirelmann_ineq (main_iter k) A (main_zero_mem_iter k) main_zero_mem_A
    have h1 : schnirelmannDensity A ≤ 1 := schnirelmannDensity_le_one
    have h2 : 0 ≤ 1 - schnirelmannDensity A := by linarith
    have h3 := mul_le_mul_of_nonneg_right (sub_le_comm.1 ih) h2
    show _ ≤ schnirelmannDensity (main_iter k + A)
    rw [pow_succ]
    nlinarith

theorem main_pow_bound (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 - 1 / 35000) : x ^ 24260 < 1 / 2 := by
  have hnat : 2 * 34999 ^ 24260 < 35000 ^ 24260 := by decide +kernel
  have hR : ((2 * 34999 ^ 24260 : ℕ) : ℝ) < ((35000 ^ 24260 : ℕ) : ℝ) := Nat.cast_lt.2 hnat
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at hR
  simp only [Nat.cast_ofNat] at hR
  have h1 : x ≤ (34999 : ℝ) / 35000 := by linarith
  have h2 : x ^ 24260 ≤ ((34999 : ℝ) / 35000) ^ 24260 := pow_le_pow_left₀ hx0 h1 _
  have h3 : ((34999 : ℝ) / 35000) ^ 24260 < 1 / 2 := by
    rw [div_pow, div_lt_iff₀ (by positivity)]
    generalize (34999 : ℝ) ^ 24260 = a at hR ⊢
    generalize (35000 : ℝ) ^ 24260 = b at hR ⊢
    linarith
  exact h2.trans_lt h3

/-- `P k t`: there are `k` odd primes summing to `2t + 3k`. -/
def main_P (k t : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.card = k ∧ (∀ p ∈ s, Nat.Prime p ∧ p ≠ 2) ∧ s.sum = 2 * t + 3 * k

theorem main_P_add {j k t u : ℕ} (h1 : main_P j t) (h2 : main_P k u) : main_P (j + k) (t + u) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h1
  obtain ⟨s', hs1', hs2', hs3'⟩ := h2
  refine ⟨s + s', by simp [hs1, hs1'], fun p hp => ?_, by simp [hs3, hs3']; ring⟩
  rcases Multiset.mem_add.1 hp with h | h
  · exact hs2 p h
  · exact hs2' p h

theorem main_P_B {b : ℕ} (hb : b ∈ B) : main_P 1 b := by
  obtain ⟨p, hp, hp2, rfl⟩ := hb
  have := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have := hp.two_le
  refine ⟨{p}, by simp, fun q hq => ?_, ?_⟩
  · rw [Multiset.mem_singleton] at hq; subst hq; exact ⟨hp, hp2⟩
  · simp; omega

theorem main_P_A {a : ℕ} (ha : a ∈ A) : main_P 2 a := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.1 ha
  exact main_P_add (main_P_B hb) (main_P_B hc)

theorem main_P_iter (k : ℕ) : ∀ t ∈ main_iter k, main_P (2 * k) t := by
  induction k with
  | zero =>
    intro t ht
    rw [main_iter, Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨0, by simp, by simp, by simp⟩
  | succ k ih =>
    intro t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 ht
    have := main_P_add (ih a ha) (main_P_A hb)
    rwa [show 2 * k + 2 = 2 * (k + 1) by ring] at this

open Classical in
theorem main_all (t : ℕ) : main_P 97040 t := by
  have hA := density_A
  have h1 : schnirelmannDensity A ≤ 1 := schnirelmannDensity_le_one
  have h3 := main_pow_bound (1 - schnirelmannDensity A) (by linarith) (by linarith)
  have hd := main_density_iter 24260
  generalize (1 - schnirelmannDensity A) ^ 24260 = y at hd h3
  have h4 : (1 : ℝ) ≤ schnirelmannDensity (main_iter 24260) + schnirelmannDensity (main_iter 24260) := by
    linarith
  have huniv : main_iter 24260 + main_iter 24260 = Set.univ :=
    add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
      (main_zero_mem_iter _) (main_zero_mem_iter _) h4
  have ht : t ∈ main_iter 24260 + main_iter 24260 := by rw [huniv]; exact Set.mem_univ t
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 ht
  exact main_P_add (main_P_iter _ a ha) (main_P_iter _ b hb)

/-- Note, Theorem 1 (exact form): every odd `n ≥ 194083` is a sum of exactly `97041` primes. -/
theorem exact_97041 (n : ℕ) (hodd : Odd n) (hn : 194083 ≤ n) :
    ∃ s : Multiset ℕ, s.card = 97041 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  by_cases hbig : 291123 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := main_all ((n - 291123) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
  · refine ⟨Multiset.replicate (n - 194082) 3 + Multiset.replicate (291123 - n) 2,
      by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hp with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

end Schnir

/-- The campaign goal (platform theorem `odd_sum_le_97041_primes`). -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 97041 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  by_cases hbig : 194083 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := Schnir.exact_97041 n hodd hbig
    exact ⟨s, hs1.le, hs2, hs3⟩
  · have hn2 := Nat.odd_iff.1 hodd
    refine ⟨3 ::ₘ Multiset.replicate ((n - 3) / 2) 2, by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

