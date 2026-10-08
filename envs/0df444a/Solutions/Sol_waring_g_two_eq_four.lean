-- Prove2me | solution 1 for waring_g_two_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:25:36.915112+00:00
-- url     : https://prove2.me/submissions/3991e83c-6b23-47e3-8e47-4c9302eceb15

import Mathlib

/-!
**Waring's problem for k = 2: g(2) = 4** (Lagrange, 1770).

Every natural number is the sum of at most four perfect squares, and four is best
possible: 7 = 4 + 1 + 1 + 1 requires all four (the only squares ≤ 7 are 0, 1, 4,
and no three of these sum to 7).

This is the k = 2 case of Waring's problem, resolved by Lagrange in 1770. The
upper bound is `Nat.sum_four_squares` in Mathlib (proved via Euler's four-square
identity and Fermat's theorem for primes). The lower bound is a finite check.
-/

theorem solution :
    (∀ n : ℕ, ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n) ∧
    ¬(∀ n : ℕ, ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n) := by
  constructor
  · intro n
    obtain ⟨a, b, c, d, rfl⟩ := Nat.sum_four_squares n
    exact ⟨a, b, c, d, rfl⟩
  · intro h
    obtain ⟨a, b, c, heq⟩ := h 7
    -- All three variables must be ≤ 2 since 3² = 9 > 7
    have hle : ∀ x : ℕ, x ^ 2 ≤ 7 → x ≤ 2 := by
      intro x hx
      by_contra hgt
      push_neg at hgt
      have : 3 ≤ x := hgt
      have : 9 ≤ x ^ 2 := by nlinarith
      omega
    have ha := hle a (by omega)
    have hb := hle b (by omega)
    have hc := hle c (by omega)
    -- Now enumerate all 27 cases (a, b, c ∈ {0, 1, 2})
    interval_cases a
    · interval_cases b
      · interval_cases c <;> omega
      · interval_cases c <;> omega
      · interval_cases c <;> omega
    · interval_cases b
      · interval_cases c <;> omega
      · interval_cases c <;> omega
      · interval_cases c <;> omega
    · interval_cases b
      · interval_cases c <;> omega
      · interval_cases c <;> omega
      · interval_cases c <;> omega
