-- Prove2me | Theorems.Thm_Erdos287_three_mersenne_bands_gap_three
-- name    : Erdos287.three_mersenne_bands_gap_three
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T17:04:26.926895+00:00
-- url     : https://prove2.me/theorems/cbf15b8d-f122-4890-9105-d9df0a179ff8
-- title:
--   Three certified Erdős 287 intervals at Mersenne primes
-- statement:
--   For $e\in\{3217,4253,4423\}$ put $q=2^e$. Every exact representation of one by distinct unit fractions with maximum denominator in $[q-1,\lfloor 1359(q-2)/500\rfloor]$ has a gap of at least three.
-- source:
--   Erdős #287 large prime-power intervals.

import Mathlib
open Finset

theorem Erdos287.three_mersenne_bands_gap_three (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (e : ℕ) (he : e = 3217 ∨ e = 4253 ∨ e = 4423)
    (hlo : 2 ^ e - 1 ≤ f (k - 1))
    (hhi : 500 * f (k - 1) ≤ 1359 * (2 ^ e - 2)) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
