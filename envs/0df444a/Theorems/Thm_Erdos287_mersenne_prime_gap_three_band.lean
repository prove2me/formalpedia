-- Prove2me | Theorems.Thm_Erdos287_mersenne_prime_gap_three_band
-- name    : Erdos287.mersenne_prime_gap_three_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T17:02:51.206949+00:00
-- url     : https://prove2.me/theorems/884cc1e3-fecb-5311-9c6d-0144c123199a
-- title:
--   An Erdős 287 band from one Mersenne prime
-- statement:
--   Let $q=2^e$ with $e\ge5$ and $q-1$ prime. Every exact representation of one by distinct unit fractions with maximum denominator $M$ satisfying $q-1\le M$ and $500M\le1359(q-2)$ has a gap of at least three.
-- source:
--   Erdős #287 large prime-power intervals.

import Mathlib
open Finset

theorem Erdos287.mersenne_prime_gap_three_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (e : ℕ) (he : 5 ≤ e) (hp : (2 ^ e - 1).Prime)
    (hlo : 2 ^ e - 1 ≤ f (k - 1))
    (hhi : 500 * f (k - 1) ≤ 1359 * (2 ^ e - 2)) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
