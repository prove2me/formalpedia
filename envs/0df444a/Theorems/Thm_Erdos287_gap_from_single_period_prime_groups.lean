-- Prove2me | Theorems.Thm_Erdos287_gap_from_single_period_prime_groups
-- name    : Erdos287.gap_from_single_period_prime_groups
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:16:42.57273+00:00
-- url     : https://prove2.me/theorems/0b23b5d6-f780-5a4d-92ce-e7db8c90037c
-- title:
--   Denominator gap from occupied affine prime groups in one period
-- statement:
--   For positive u and u at most v less than exp(1) times u, with 2u at most v+2, there exist exactly u+v groups of K affine prime forms and one relative parameter window. If more than u groups have a prime at a common parameter in that window, every sufficiently large Egyptian fraction representation under consideration has a consecutive denominator gap of at least three.
-- source:
--   Erdős Problem #287. Strengthens the grouped prime occupancy reduction using the sharp packing bound on a single interval.

import Mathlib

theorem Erdos287.gap_from_single_period_prime_groups (N K u v : ℕ) (hN : N = u + v) (hK : 0 < K) (hu : 0 < u) (huv : u ≤ v)
    (hv : 2 * u ≤ v + 2) (hve : (v : ℝ) < Real.exp 1 * u) :
    ∃ (b : ℕ → ℕ → ℕ) (α β : ℝ) (M₀ : ℕ), 0 < α ∧ α < β ∧
      (∀ s < N, ∀ j < K, 0 < b s j) ∧
      (∀ s r i j, s < N → r < N → i < K → j < K →
        b s i = b r j → s = r ∧ i = j) ∧
      ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
        (∀ i, i < k → 1 < f i) →
        (∀ i j, i < j → j < k → f i < f j) →
        (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) →
        M₀ ≤ f (k - 1) →
        ∀ t : ℕ, α * (f (k - 1) : ℝ) ≤ t → (t : ℝ) ≤ β * f (k - 1) →
        u < ((Finset.range N).filter fun s => ∃ j : Fin K, Nat.Prime (b s j * t + 1)).card →
        ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
