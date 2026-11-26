-- Prove2me | solution 1 for edenic_semiprime_gcd_sigma
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T23:37:50.286413+00:00
-- url     : https://prove2.me/submissions/c0fdc0b2-a06f-4cbc-8f74-d884265f3925

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_sum_divisors

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n.Coprime (∑ d ∈ n.divisors, d) ∨ n = 15 := by
  obtain ⟨p, hp, hp2, rfl, hsum⟩ := edenic_semiprime_sum_divisors _ h
  rw [hsum]
  by_cases hc : Nat.Coprime (p * (p + 2)) ((p + 1) * (p + 3))
  · exact Or.inl hc
  · rcases Nat.Prime.not_coprime_iff_dvd.mp hc with ⟨q, hq, hqn, hqs⟩
    rcases (Nat.Prime.dvd_mul hq).mp hqn with h1 | h1
    · have qe : p = q := (Nat.Prime.dvd_iff_eq hp hq.ne_one).mp h1
      subst qe
      rcases (Nat.Prime.dvd_mul hp).mp hqs with h2 | h2
      · have hd : p ∣ (p + 1) - p := Nat.dvd_sub h2 dvd_rfl
        simp at hd
        exact absurd hd (by exact_mod_cast hp.ne_one)
      · have hd : p ∣ (p + 3) - p := Nat.dvd_sub h2 dvd_rfl
        simp at hd
        rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
        · exact absurd h (by exact_mod_cast hp.ne_one)
        · exact Or.inr (by rw [h])
    · have qe : p + 2 = q := (Nat.Prime.dvd_iff_eq hp2 hq.ne_one).mp h1
      subst qe
      rcases (Nat.Prime.dvd_mul hp2).mp hqs with h2 | h2
      · have hd : p + 2 ∣ (p + 2) - (p + 1) := Nat.dvd_sub dvd_rfl h2
        simp at hd
      · have hd : p + 2 ∣ (p + 3) - (p + 2) := Nat.dvd_sub h2 dvd_rfl
        simp at hd
