-- Prove2me | solution 1 for factorial_perfect_power
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:20:12.339632+00:00
-- url     : https://prove2.me/submissions/aa4d48ca-9f78-45a9-a171-651b25f066b9

import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

theorem solution :
    {(n, m, k) : ℕ × ℕ × ℕ | 1 ≤ n ∧ 2 ≤ m ∧ 2 ≤ k ∧ n.factorial = m ^ k}.Finite := by
  have hempty :
      {(n, m, k) : ℕ × ℕ × ℕ | 1 ≤ n ∧ 2 ≤ m ∧ 2 ≤ k ∧ n.factorial = m ^ k} = ∅ := by
    ext ⟨n, m, k⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hn, hm, hk, h⟩
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- `n = 1`: then `1 = m ^ k ≥ 2 ^ 2`.
      have hn1 : n = 1 := by omega
      subst hn1
      have h4 : 2 ^ 2 ≤ m ^ k :=
        calc 2 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
          _ ≤ m ^ k := Nat.pow_le_pow_right (by omega) hk
      rw [← h] at h4
      simp at h4
    · -- Bertrand: a prime `p` with `n / 2 < p ≤ 2 * (n / 2) ≤ n`, hence `p ≤ n < 2 * p`.
      obtain ⟨p, hp, hqp, hp2q⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
      have hpn : p ≤ n := by omega
      have hn2p : n < 2 * p := by omega
      have hp2 : 2 ≤ p := hp.two_le
      -- `p ∣ n!` forces `p ∣ m`, hence `p ^ 2 ∣ m ^ k = n!`.
      have hdvd : p ∣ n.factorial := (Nat.Prime.dvd_factorial hp).mpr hpn
      rw [h] at hdvd
      have hpm : p ∣ m := hp.dvd_of_dvd_pow hdvd
      have hp2dvd : p ^ 2 ∣ n.factorial := by
        rw [h]
        exact (pow_dvd_pow_of_dvd hpm 2).trans (pow_dvd_pow m hk)
      -- But the exponent of `p` in `n!` is `⌊n / p⌋ = 1` (Legendre), since `n < p ^ 2`.
      have hlog : Nat.log p n < 2 := by
        rw [Nat.log_lt_iff_lt_pow hp.one_lt (by omega)]
        nlinarith
      rw [Nat.Prime.pow_dvd_factorial_iff hp hlog] at hp2dvd
      have hsum : ∑ i ∈ Finset.Ico 1 2, n / p ^ i = n / p := by
        rw [Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty, zero_add,
          pow_one]
      rw [hsum] at hp2dvd
      have hdiv : n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      omega
  rw [hempty]
  exact Set.finite_empty
