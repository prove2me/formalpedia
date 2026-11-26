-- Prove2me | Theorems.Thm_Erdos287_opposite_parity_holes_enclose_even_run
-- name    : Erdos287.opposite_parity_holes_enclose_even_run
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:59:54.326719+00:00
-- url     : https://prove2.me/theorems/1f83bae2-9600-45b0-bab5-59e1138ec338
-- title:
--   Opposite-parity omissions enclose an even selected run
-- statement:
--   Let $H$ be a finite set of omitted positions with no consecutive integers. If $a<b$ are omissions of opposite parity, then between them there are consecutive omissions $x<y$ with $y-x-1$ positive and even. In particular their intervening selected run has at least two positions.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.opposite_parity_holes_enclose_even_run (H : Finset ℕ) (a b : ℕ) (ha : a ∈ H) (hb : b ∈ H) (hab : a < b)
    (hp : a % 2 ≠ b % 2) (hsep : ∀ n ∈ H, n + 1 ∉ H) :
    ∃ x ∈ H, ∃ y ∈ H, a ≤ x ∧ y ≤ b ∧ x + 3 ≤ y ∧ Even (y - x - 1) ∧
      ∀ n, x < n → n < y → n ∉ H := by sorry
