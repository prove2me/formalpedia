-- Prove2me | Theorems.Thm_Erdos287_gap_from_weighted_group_moments
-- name    : Erdos287.gap_from_weighted_group_moments
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:06:12.757089+00:00
-- url     : https://prove2.me/theorems/94a51c62-b1a7-5ff5-8d99-5863921426aa
-- title:
--   A first and second moment criterion for a denominator gap
-- statement:
--   In the affine prime-form group reduction of Erdős #287, give the parameters in the prescribed window nonnegative weights. Let W be the total weight, J the weighted sum of prime counts over all groups, and Q the weighted sum of squared prime counts within groups. If u(N+v) WQ < (u+v) J^2, the original denominator sequence has a gap of at least three.
-- source:
--   Erdős Problem #287, refinement of the grouped prime occupancy reduction [74c37d05-32ed-401f-8f83-dd30fe7e6db0].

import Mathlib

theorem Erdos287.gap_from_weighted_group_moments (N K u v : ℕ) (hK : 0 < K) (hu : 0 < u) (huv : u ≤ v)
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
        ∀ (T : Finset ℕ) (w : ℕ → ℝ),
          (∀ t ∈ T, α * (f (k - 1) : ℝ) ≤ t ∧ (t : ℝ) ≤ β * f (k - 1)) →
          (∀ t ∈ T, 0 ≤ w t) →
          let m (t s : ℕ) : ℝ :=
            ((Finset.univ.filter fun j : Fin K => Nat.Prime (b s j * t + 1)).card : ℝ)
          let W := ∑ t ∈ T, w t
          let J := ∑ t ∈ T, w t * ∑ s ∈ Finset.range N, m t s
          let Q := ∑ t ∈ T, w t * ∑ s ∈ Finset.range N, m t s ^ 2
          (u : ℝ) * ((N : ℝ) + v) * W * Q < ((u : ℝ) + v) * J ^ 2 →
          ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
