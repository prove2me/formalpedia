-- Prove2me | Theorems.Thm_Erdos287_power_of_two_slopes_have_opposite_parity_multiples
-- name    : Erdos287.power_of_two_slopes_have_opposite_parity_multiples
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:20:47.546685+00:00
-- url     : https://prove2.me/theorems/43aa28e4-af57-4bf8-aff1-3cff085c5c5c
-- title:
--   Opposite-parity multiples from power-of-two slopes
-- statement:
--   Let \(i<j<N\le L\) and let \(t\) be a natural number. There are a positive odd \(b\) and a larger even \(a\le 2^L+2^N\) such that \(a(2^it+1)=(2^L+2^j)t+a\) and \(b(2^jt+1)=(2^L+2^j)t+b\).
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Maynard, Dense clusters of primes in subsets, https://arxiv.org/abs/1405.2593.

import Mathlib

theorem Erdos287.power_of_two_slopes_have_opposite_parity_multiples (N L i j t : ℕ) (hL : N ≤ L) (hij : i < j) (hj : j < N) :
    ∃ a b : ℕ,
      a % 2 = 0 ∧ b % 2 = 1 ∧
      0 < b ∧ b < a ∧ a ≤ 2 ^ L + 2 ^ N ∧
      a * (2 ^ i * t + 1) = (2 ^ L + 2 ^ j) * t + a ∧
      b * (2 ^ j * t + 1) = (2 ^ L + 2 ^ j) * t + b := by sorry
