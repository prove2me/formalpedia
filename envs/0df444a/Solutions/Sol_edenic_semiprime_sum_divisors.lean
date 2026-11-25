-- Prove2me | solution 1 for edenic_semiprime_sum_divisors
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T17:35:47.18988+00:00
-- url     : https://prove2.me/submissions/1e618d31-058b-4335-86ec-a5fed52bb2ae

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧
      ∑ d ∈ n.divisors, d = (p + 1) * (p + 3) := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  refine ⟨p, hp, hp2, rfl, ?_⟩
  have hc : p.Coprime (p + 2) := twin_primes_coprime p hp hp2
  rw [Nat.Coprime.sum_divisors_mul hc, Nat.Prime.divisors hp, Nat.Prime.divisors hp2,
    Finset.sum_pair hp.ne_one.symm, Finset.sum_pair hp2.ne_one.symm]
  ring
