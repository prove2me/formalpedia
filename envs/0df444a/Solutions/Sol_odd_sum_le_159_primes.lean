-- Prove2me | solution 1 for odd_sum_le_159_primes
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-05T02:42:31.200722+00:00
-- url     : https://prove2.me/submissions/854d6bec-818a-4fe8-b4ec-2ca6e760eb7c

import Mathlib
import Theorems.Thm_odd_sum_le_151_primes

/-- At most `159` primes, from the proved bound `151`. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 159 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  obtain ⟨s, hs1, hs2, hs3⟩ := odd_sum_le_151_primes n hodd hn
  exact ⟨s, by omega, hs2, hs3⟩
