-- Prove2me | solution 1 for semiprimes_infinite
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T01:34:09.168808+00:00
-- url     : https://prove2.me/submissions/e32ad891-557c-40b9-babf-c9756c2858cf

import Mathlib

/-! # There are infinitely many semiprimes

Target `semiprimes_infinite`. Every prime square `p²` is a semiprime
(`Nat.Prime.sq_isAlmostPrime_two`); primes are unbounded above, so the semiprimes are too. -/

theorem solution : {n : ℕ | Nat.IsSemiprime n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro a
  obtain ⟨p, hp, hlt⟩ : ∃ p, p.Prime ∧ a < p := by
    simpa using not_bddAbove_iff.1 Nat.not_bddAbove_setOfPred_prime a
  exact ⟨p ^ 2, Nat.Prime.sq_isAlmostPrime_two hp,
    by rw [pow_two]; nlinarith [hp.two_le]⟩
