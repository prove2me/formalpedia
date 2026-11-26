-- Prove2me | Theorems.Thm_Erdos287_three_power_endpoint_neighbors
-- name    : Erdos287.three_power_endpoint_neighbors
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:08:17.204734+00:00
-- url     : https://prove2.me/theorems/86e09008-27d1-5d4c-a263-7054b54f6ba3
-- title:
--   Prime-power half-neighbors cannot occur at the three-powered exceptional endpoint
-- statement:
--   Suppose a finite set of denominators with least $m$, largest $M=6\cdot3^j$, reciprocal sum one, and $M<3m$ omits no adjacent pair in $[m,M]$. If $j\ge1$, both $5\cdot3^j-1$ and $5\cdot3^j+1$ are selected and neither can be twice a positive power of a prime.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.three_power_endpoint_neighbors (D : Finset ℕ) (m j : ℕ) (hm : 0 < m) (hj : 1 ≤ j)
    (hD : D ⊆ Finset.Icc m (6 * 3 ^ j)) (hmD : m ∈ D) (hMD : 6 * 3 ^ j ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) (hratio : 6 * 3 ^ j < 3 * m)
    (hcover : ∀ n, m ≤ n → n + 1 ≤ 6 * 3 ^ j → n ∈ D ∨ (n + 1) ∈ D) :
    let r := 3 ^ j
    (5 * r - 1) ∈ D ∧ (5 * r + 1) ∈ D ∧
      ∀ p a : ℕ, p.Prime → 1 ≤ a → 2 * p ^ a ≠ 5 * r - 1 ∧ 2 * p ^ a ≠ 5 * r + 1 := by sorry
