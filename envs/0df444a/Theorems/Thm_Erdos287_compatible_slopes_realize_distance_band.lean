-- Prove2me | Theorems.Thm_Erdos287_compatible_slopes_realize_distance_band
-- name    : Erdos287.compatible_slopes_realize_distance_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:40:42.249628+00:00
-- url     : https://prove2.me/theorems/81142931-16c8-56d9-b8e0-7057d2f5e41c
-- title:
--   Compatible affine slopes realizing a prescribed distance band
-- statement:
--   Fix strictly increasing natural positions $z_0,\ldots,z_{n-1}$ and $0<u\le v<\mathrm e u$. There exist increasing positive natural slopes $a_0,\ldots,a_{n-1}$ and real $0<L\le U<\mathrm e L$ such that for every $i<j<n$, $a_j-a_i$ divides $a_i$. Whenever $u\le z_j-z_i\le v$, the coefficient $a_i a_j/(a_j-a_i)$ is in $[L,U]$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. The base divisibility construction extends Heath-Brown’s lemma as given in Ford, Sieve Methods, Lemma 7.20, https://ford126.web.illinois.edu/sieve2023.pdf.

import Mathlib

theorem Erdos287.compatible_slopes_realize_distance_band (n : ℕ) (z : ℕ → ℕ) (hz : StrictMono z)
    (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v < Real.exp 1 * u) :
    ∃ (a : ℕ → ℕ) (L U : ℝ), 0 < L ∧ L ≤ U ∧ U < Real.exp 1 * L ∧
      (∀ i < n, 0 < a i) ∧
      ∀ i j, i < j → j < n →
        a i < a j ∧ (a j - a i) ∣ a i ∧
        (u ≤ (z j : ℝ) - z i → (z j : ℝ) - z i ≤ v →
          L ≤ ((a i / (a j - a i) : ℕ) : ℝ) * a j ∧
          ((a i / (a j - a i) : ℕ) : ℝ) * a j ≤ U) := by sorry
