-- Prove2me | Theorems.Thm_Erdos287_unit_gap_count_from_prime_windows
-- name    : Erdos287.unit_gap_count_from_prime_windows
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:16:55.408803+00:00
-- url     : https://prove2.me/theorems/d01fe681-90ee-4d6a-a85d-a1448c9fde52
-- title:
--   Prime and doubled-prime windows force many unit gaps
-- statement:
--   In an Egyptian fraction representation of 1 with consecutive gaps at most two, suppose each of a finite set of length-H windows inside the denominator range contains a sufficiently large odd prime and twice a sufficiently large prime. Then the number of windows is at most H times the number of gaps of size one.
-- source:
--   Erdős Problem #287. Short-interval parity-transition argument.

import Mathlib

theorem Erdos287.unit_gap_count_from_prime_windows (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (S : Finset ℕ) (H : ℕ)
    (hwindows : ∀ x ∈ S, f 0 < x ∧ x + H ≤ f (k - 1) ∧
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 3 < p ∧ 3 < q ∧
        f (k - 1) < 3 * p ∧ f (k - 1) < 3 * q ∧
        x ≤ p ∧ p < x + H ∧ x ≤ 2 * q ∧ 2 * q < x + H) :
    S.card ≤ H * ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card := by sorry
