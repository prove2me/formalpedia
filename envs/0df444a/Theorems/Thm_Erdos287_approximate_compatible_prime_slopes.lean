-- Prove2me | Theorems.Thm_Erdos287_approximate_compatible_prime_slopes
-- name    : Erdos287.approximate_compatible_prime_slopes
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:53:39.449799+00:00
-- url     : https://prove2.me/theorems/a6d88d98-1095-402d-ad91-3ffb312fc713
-- title:
--   Compatible affine prime slopes approximate a prescribed finite geometry
-- statement:
--   For every strictly increasing natural sequence of positions $z_i$ and every $0<\delta\le1$, there are natural slopes $a_i$ for the first $n$ positions and positive scales $A,C$ such that $A\le a_i\le(1+\delta)A$, $a_j-a_i$ is positive and divides $a_i$ for $i<j<n$, and $|(a_j-a_i)/C-(z_j-z_i)|<\delta$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Quantitative core of the compatible slope and distance-band construction.

import Mathlib

theorem Erdos287.approximate_compatible_prime_slopes (n : ℕ) (z : ℕ → ℕ) (hz : StrictMono z)
    (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ a : ℕ → ℕ, ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      (∀ i < n, A ≤ (a i : ℝ) ∧ (a i : ℝ) ≤ (1 + δ) * A) ∧
      ∀ i j, i < j → j < n → a i < a j ∧ (a j - a i) ∣ a i ∧
        |((a j - a i : ℕ) : ℝ) / C - ((z j : ℝ) - z i)| < δ := by sorry
