-- Prove2me | solution 1 for odd_sum_le_4401_primes
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:28:25.417693+00:00
-- url     : https://prove2.me/submissions/84a89dfd-ea71-4fc3-89ef-34c0f65b23df

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_density_A_2200
import Theorems.Thm_Schnirelmann_mann

/-!
Every odd `n > 1` is a sum of at most `4401` primes.

Improves the proved `odd_sum_le_6101_primes` entry of the odd-Goldbach campaign by
replacing the multiplicative Schnirelmann iteration `σ(hA) ≥ 1 - (1 - σ(A))^h`
(with `m = 1525` and a kernel-checked power bound) by the additive Mann iteration
`σ(hA) ≥ min 1 (h * σ(A))`:

* `σ(A) ≥ 1/2200` (`Schnir.density_A_2200`, extracted from the 6101 solution);
* Mann's theorem `σ(D + E) ≥ min 1 (σ D + σ E)` (`Schnirelmann.mann`, Dyson transform),
  iterated `1100` times, gives `σ(1100 A) ≥ 1/2`;
* the cover lemma `add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity`
  then gives `1100 A + 1100 A = ℕ`, i.e. every `t` is a sum of two elements of `1100 A`,
  each of which is `4400 = 2 * 1100` odd primes summing to `2t + 13200`;
* so every odd `n ≥ 13203` is `3` plus `4400` odd primes; odd `8803 ≤ n ≤ 13201` are
  exactly `4401` primes of `3`s and `2`s; odd `3 ≤ n ≤ 8801` are `3` plus `(n-3)/2` twos.
-/

open Finset Real Pointwise

namespace Schnir

/-- Iterated sumsets `iter k = k A` (with `iter 0 = {0}`). -/
def iter : ℕ → Set ℕ
  | 0 => {0}
  | k + 1 => iter k + A

theorem zero_mem_A : (0 : ℕ) ∈ A :=
  Set.mem_add.2 ⟨0, ⟨3, Nat.prime_three, by norm_num, rfl⟩, 0, ⟨3, Nat.prime_three, by norm_num, rfl⟩,
    rfl⟩

theorem zero_mem_iter (k : ℕ) : 0 ∈ iter k := by
  induction k with
  | zero => rfl
  | succ k ih => exact Set.mem_add.2 ⟨0, ih, 0, zero_mem_A, rfl⟩

open Classical in
/-- **Mann iteration:** `σ(kA) ≥ min 1 (k * σ(A))`, by induction on `k`, applying Mann's
theorem `σ(D + E) ≥ min 1 (σ D + σ E)` at each step. -/
theorem mann_iter (k : ℕ) :
    min 1 ((k : ℝ) * schnirelmannDensity A) ≤ schnirelmannDensity (iter k) := by
  induction k with
  | zero =>
    have h1 : 1 ∉ (iter 0 : Set ℕ) := by simp [iter]
    have h0 := schnirelmannDensity_eq_zero_of_one_notMem h1
    simp only [Nat.cast_zero, zero_mul, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    linarith
  | succ k ih =>
    show _ ≤ schnirelmannDensity (iter k + A)
    rw [Nat.cast_succ, add_mul, one_mul]
    have hσ0 : 0 ≤ schnirelmannDensity A := schnirelmannDensity_nonneg
    have hstep1 : min 1 ((k : ℝ) * schnirelmannDensity A + schnirelmannDensity A)
        ≤ min 1 (min 1 ((k : ℝ) * schnirelmannDensity A) + schnirelmannDensity A) := by
      rcases le_total 1 ((k : ℝ) * schnirelmannDensity A) with h | h
      · rw [min_eq_left (by linarith), min_eq_left h, min_eq_left (by linarith)]
      · rw [min_eq_right h]
    have hkey2 : min 1 ((k : ℝ) * schnirelmannDensity A) + schnirelmannDensity A
        ≤ schnirelmannDensity (iter k) + schnirelmannDensity A := by linarith
    have hmann : min 1 (schnirelmannDensity (iter k) + schnirelmannDensity A)
        ≤ schnirelmannDensity (iter k + A) :=
      Schnirelmann.mann (iter k) A (zero_mem_iter k) zero_mem_A
    calc min 1 ((k : ℝ) * schnirelmannDensity A + schnirelmannDensity A)
        ≤ min 1 (min 1 ((k : ℝ) * schnirelmannDensity A) + schnirelmannDensity A) := hstep1
      _ ≤ min 1 (schnirelmannDensity (iter k) + schnirelmannDensity A) :=
          min_le_min le_rfl hkey2
      _ ≤ schnirelmannDensity (iter k + A) := hmann

/-- `P k t`: there are `k` odd primes summing to `2t + 3k`. -/
def P (k t : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.card = k ∧ (∀ p ∈ s, Nat.Prime p ∧ p ≠ 2) ∧ s.sum = 2 * t + 3 * k

theorem P_add {j k t u : ℕ} (h1 : P j t) (h2 : P k u) : P (j + k) (t + u) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h1
  obtain ⟨s', hs1', hs2', hs3'⟩ := h2
  refine ⟨s + s', by simp [hs1, hs1'], fun p hp => ?_, by simp [hs3, hs3']; ring⟩
  rcases Multiset.mem_add.1 hp with h | h
  · exact hs2 p h
  · exact hs2' p h

theorem P_B {b : ℕ} (hb : b ∈ B) : P 1 b := by
  obtain ⟨p, hp, hp2, rfl⟩ := hb
  have := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have := hp.two_le
  refine ⟨{p}, by simp, fun q hq => ?_, ?_⟩
  · rw [Multiset.mem_singleton] at hq; subst hq; exact ⟨hp, hp2⟩
  · simp; omega

theorem P_A {a : ℕ} (ha : a ∈ A) : P 2 a := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.1 ha
  exact P_add (P_B hb) (P_B hc)

theorem P_iter (k : ℕ) : ∀ t ∈ iter k, P (2 * k) t := by
  induction k with
  | zero =>
    intro t ht
    rw [iter, Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨0, by simp, by simp, by simp⟩
  | succ k ih =>
    intro t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 ht
    have := P_add (ih a ha) (P_A hb)
    rwa [show 2 * k + 2 = 2 * (k + 1) by ring] at this

open Classical in
/-- Every `t` is a sum of `4400` odd primes plus `6 * 2200` — the Mann-based replacement
for the product-iteration step of the 6101 proof. -/
theorem all_4400 (t : ℕ) : P 4400 t := by
  have hd : (1 : ℝ) / 2200 ≤ schnirelmannDensity A := density_A_2200
  have hiter := mann_iter 1100
  have hhalf : (1 : ℝ) / 2 ≤ schnirelmannDensity (iter 1100) := by
    have hmin : (1 : ℝ) / 2 ≤ min 1 (((1100 : ℕ) : ℝ) * schnirelmannDensity A) := by
      refine le_min (by norm_num) ?_
      have h1100 : (((1100 : ℕ) : ℝ) * ((1 : ℝ) / 2200)) = 1 / 2 := by push_cast; norm_num
      have hle : (((1100 : ℕ) : ℝ) * ((1 : ℝ) / 2200))
          ≤ (((1100 : ℕ) : ℝ) * schnirelmannDensity A) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      linarith
    exact hmin.trans hiter
  have hsum : (1 : ℝ) ≤ schnirelmannDensity (iter 1100)
      + schnirelmannDensity (iter 1100) := by linarith
  have huniv : iter 1100 + iter 1100 = Set.univ :=
    add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
      (zero_mem_iter _) (zero_mem_iter _) hsum
  have ht : t ∈ iter 1100 + iter 1100 := by rw [huniv]; exact Set.mem_univ t
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 ht
  exact P_add (P_iter _ a ha) (P_iter _ b hb)

end Schnir

/-- The campaign goal: every odd `n > 1` is a sum of at most `4401` primes. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 4401 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  rcases Nat.lt_or_ge n 13203 with hsmall | hlarge
  · rcases Nat.lt_or_ge n 8803 with hsmall' | hmid
    · -- `3 ≤ n ≤ 8801`: a 3 plus `(n-3)/2` twos, at most 4400 primes
      refine ⟨3 ::ₘ Multiset.replicate ((n - 3) / 2) 2, by simp; omega, fun p hp => ?_, ?_⟩
      · rcases Multiset.mem_cons.1 hp with h | h
        · rw [h]; exact Nat.prime_three
        · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
      · simp; omega
    · -- `8803 ≤ n ≤ 13201`: exactly 4401 primes, all 3s and 2s
      refine ⟨Multiset.replicate (n - 8802) 3 + Multiset.replicate (13203 - n) 2,
        by simp; omega, fun p hp => ?_, ?_⟩
      · rcases Multiset.mem_add.1 hp with h | h
        · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
        · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
      · simp; omega
  · -- `n ≥ 13203`: a 3 plus 4400 odd primes via Mann ×1100 and the cover lemma
    obtain ⟨s, hs1, hs2, hs3⟩ := Schnir.all_4400 ((n - 13203) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
