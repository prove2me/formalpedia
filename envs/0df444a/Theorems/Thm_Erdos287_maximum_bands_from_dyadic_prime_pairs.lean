-- Prove2me | Theorems.Thm_Erdos287_maximum_bands_from_dyadic_prime_pairs
-- name    : Erdos287.maximum_bands_from_dyadic_prime_pairs
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:55:09.882433+00:00
-- url     : https://prove2.me/theorems/5eae58b3-d24c-40ff-9eec-262190f35e18
-- title:
--   Bands of Egyptian-fraction maxima from dyadic prime pairs
-- statement:
--   Suppose $N\ge2$ has this prime-supply property. For every fixed tuple of $N$ distinct increasing positive integers $a_i$, every sufficiently large interval $[V,2V]$ contains an integer $t$ with at least two prime values $a_i t+1$.
--
--   Then for every sufficiently large integer $T$ there exists $x\ge T$ with $2x\le(12N+2)T$ such that every unit-fraction representation of one with distinct increasing denominators greater than one and maximum in $[x+1,2x]$ has a consecutive gap of at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. The prime-supply input is the general-affine version of Maynard–Tao stated in Ford, Sieve Methods, Theorem 7.6, https://ford126.web.illinois.edu/sieve2023.pdf.

import Mathlib

theorem Erdos287.maximum_bands_from_dyadic_prime_pairs (N : ℕ) (hN : 2 ≤ N)
    (hpair_supply : ∀ a : ℕ → ℕ, (∀ i < N, 0 < a i) →
      (∀ i j, i < j → j < N → a i < a j) →
      ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → ∃ t : ℕ, T ≤ t ∧ t ≤ 2 * T ∧
        ∃ i j, i < j ∧ j < N ∧ Nat.Prime (a i * t + 1) ∧ Nat.Prime (a j * t + 1)) :
    ∃ T₁ : ℕ, ∀ T : ℕ, T₁ ≤ T →
      ∃ x : ℕ, T ≤ x ∧ 2 * x ≤ (12 * N + 2) * T ∧
        ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
          (∀ i, i < k → 1 < f i) →
          (∀ i j, i < j → j < k → f i < f j) →
          (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) →
          x + 1 ≤ f (k - 1) → f (k - 1) ≤ 2 * x →
          ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
