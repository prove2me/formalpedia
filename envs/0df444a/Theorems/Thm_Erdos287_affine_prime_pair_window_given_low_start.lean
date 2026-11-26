-- Prove2me | Theorems.Thm_Erdos287_affine_prime_pair_window_given_low_start
-- name    : Erdos287.affine_prime_pair_window_given_low_start
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:52:17.250888+00:00
-- url     : https://prove2.me/theorems/a2bf170d-5ae6-5da0-b5ce-4c59123311c3
-- title:
--   A prime-pair window using the smallest denominator
-- statement:
--   Given positive \(\rho,L\) and \(L\le U<\rho L\), there is a fixed relative parameter window for all sufficiently large maxima \(M\). Suppose a representation of \(1\) has smallest denominator \(m\) with \(\rho m\le M\). In that window, two prime values \(at+1,bt+1\) of bounded compatible slopes \(a<b\), with \(L\le(a/(b-a))b\le U\), imply a gap at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Affine prime-pair transfer taking the smallest denominator into account.

import Mathlib

theorem Erdos287.affine_prime_pair_window_given_low_start (A : ℕ) (L U ρ : ℝ) (hρ : 0 < ρ) (hL : 0 < L)
    (hLU : L ≤ U) (hU : U < ρ * L) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ ∃ M₀ : ℕ,
      ∀ (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ),
        (∀ i, i < k → 1 < f i) →
        (∀ i j, i < j → j < k → f i < f j) →
        (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) →
        ρ * (f 0 : ℝ) ≤ (f (k - 1) : ℝ) →
        M₀ ≤ f (k - 1) →
        ∀ (a b t : ℕ), 0 < a → a < b → b ≤ A → (b - a) ∣ a →
          α * (f (k - 1) : ℝ) ≤ t → (t : ℝ) ≤ β * f (k - 1) →
          L ≤ ((a / (b - a) : ℕ) : ℝ) * b →
          ((a / (b - a) : ℕ) : ℝ) * b ≤ U →
          Nat.Prime (a * t + 1) → Nat.Prime (b * t + 1) →
          ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
