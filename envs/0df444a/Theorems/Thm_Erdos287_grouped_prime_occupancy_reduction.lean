-- Prove2me | Theorems.Thm_Erdos287_grouped_prime_occupancy_reduction
-- name    : Erdos287.grouped_prime_occupancy_reduction
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:42:30.560673+00:00
-- url     : https://prove2.me/theorems/74c37d05-32ed-401f-8f83-dd30fe7e6db0
-- title:
--   Fixed grouped prime forms for the Erdős 287 occupancy reduction
-- statement:
--   Fix group count $N$ and group size $K>0$, and integers $0<u\le v$ with $2u\le v+2$ and $v<\mathrm e u$. There are $N K$ distinct positive integer slopes $b_{s,j}$, with $N$ groups of size $K$, and constants $0<\alpha<\beta$ and $M_0$, with the following property.
--
--   Let $1<n_0<\cdots<n_{k-1}=M$ be a unit-fraction representation of one with $M\ge M_0$. If there is an integer $t\in[\alpha M,\beta M]$ such that the number of groups $S$ containing a prime $b_{s,j}t+1$ satisfies $(u+v)|S|>u(N+v)$, then some consecutive denominator gap is at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Uses Erdos287.compatible_slopes_realize_distance_band and Erdos287.gap_from_uniform_prime_window.

import Mathlib

theorem Erdos287.grouped_prime_occupancy_reduction (N K u v : ℕ) (hK : 0 < K) (hu : 0 < u) (huv : u ≤ v)
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
        u * (N + v) < (u + v) *
          ((Finset.range N).filter fun s => ∃ j : Fin K, Nat.Prime (b s j * t + 1)).card →
        ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
