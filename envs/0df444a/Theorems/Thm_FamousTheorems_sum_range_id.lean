-- Prove2me | Theorems.Thm_FamousTheorems_sum_range_id
-- name    : FamousTheorems.sum_range_id
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:22.743275+00:00
-- url     : https://prove2.me/theorems/d72619c4-8bdd-45ef-bc44-626e2562287a
-- title:
--   The sum of an arithmetic series
-- statement:
--   **The sum of the first $n$ natural numbers.**
--
--   $$0 + 1 + \cdots + (n-1) \;=\; \frac{n(n-1)}{2}.$$
--
--   Pairing the first and last terms, the second and second-to-last, and so on gives $n/2$ pairs each
--   summing to $n-1$ — the argument attributed to the schoolboy Gauss.
--
--   It is the case $d = 1$ of the arithmetic series formula and the first of the power sums
--   $\sum i^k$, whose general form involves Bernoulli numbers.
--
--   **Formalization note.** The sum runs over `Finset.range n` $= \{0,\dots,n-1\}$, and the division
--   is natural-number division, exact here since $n(n-1)$ is always even.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sum_range_id : ∀ n : ℕ, ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 := by sorry

end FamousTheorems
