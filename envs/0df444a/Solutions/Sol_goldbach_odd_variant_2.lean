-- Prove2me | solution 2 for goldbach_odd_variant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-10T12:34:50.936858+00:00
-- url     : https://prove2.me/submissions/94dd8bcb-12aa-4af7-a90f-2acde4624f73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30

theorem solution :
    ∀ n : ℕ, 7 < n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  intro n hn hnot
  have hnotEven : ¬ Even n := by
    intro heven
    exact hnot heven.two_dvd
  have hodd : Odd n := Nat.not_even_iff_odd.mp hnotEven
  by_cases hlarge : 10 ^ 27 ≤ n
  · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.three_odd_primes_ge_10pow27 n hlarge hodd
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
  · have hsmall : n < 10 ^ 27 := Nat.lt_of_not_ge hlarge
    have hlo : 7 ≤ n := by omega
    have hverified : n ≤ 8875694145621773516800000000000 := by
      exact le_trans (Nat.le_of_lt hsmall) (by norm_num)
    obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
      WeakGoldbach.verified_three_primes_to_8875e30 n hlo hverified hodd
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
