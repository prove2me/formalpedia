-- Prove2me | Theorems.Thm_Erdos287_prime_midpoint_requires_two_unmatched_omissions
-- name    : Erdos287.prime_midpoint_requires_two_unmatched_omissions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:51:55.118855+00:00
-- url     : https://prove2.me/theorems/3174764c-6d13-43e5-8eba-01f91ace052f
-- title:
--   A prime midpoint forces at least two unmatched omissions
-- statement:
--   Consider a set of distinct denominators in $[m,M]$ with reciprocal sum one and no two consecutive omissions, where $1<m<M$. If the midpoint is a prime $p$, then at least two omitted nonmultiples of $p$ have their reflections present among the denominators.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.prime_midpoint_requires_two_unmatched_omissions (D : Finset ℕ) (m M p : ℕ) (hm : 1 < m) (hspan : m < M)
    (hp : p.Prime) (hcenter : m + M = 2 * p)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hcover : ∀ n, m ≤ n → n + 1 ≤ M → n ∈ D ∨ n + 1 ∈ D) :
    let H := ((Finset.Icc m M).filter (fun n => ¬ p ∣ n)) \ D
    2 ≤ (H.filter (fun n => m + M - n ∉ H)).card := by sorry
