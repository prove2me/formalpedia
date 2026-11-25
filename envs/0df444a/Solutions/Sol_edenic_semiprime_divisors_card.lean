-- Prove2me | solution 1 for edenic_semiprime_divisors_card
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T07:29:22.573195+00:00
-- url     : https://prove2.me/submissions/4d79a3ba-2b56-4e56-9592-e45224304597

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    (Nat.divisors n).card = 4 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hc : p.Coprime (p + 2) := twin_primes_coprime p hp hp2
  have hp3 : 2 ≤ p := hp.two_le
  have h1 : (1 : ℕ) ≠ p := by omega
  have h2 : (1 : ℕ) ≠ p + 2 := by omega
  rw [Nat.Coprime.divisors_mul hc, Finset.card_map, Finset.card_attach, Finset.card_product,
    Nat.Prime.divisors hp, Nat.Prime.divisors hp2, Finset.card_pair h1, Finset.card_pair h2]
