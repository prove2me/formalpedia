-- Prove2me | Theorems.Thm_AppliedComb_InclExcl_derangements_count
-- name    : AppliedComb.InclExcl.derangements_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:10:23.320996+00:00
-- url     : https://prove2.me/theorems/08caa73f-6e62-496e-ae7e-dffab999506e
-- title:
--   Theorem 7.11 — The number of derangements of [n]
-- statement:
--   A **derangement** of $[n]$ is a permutation $\sigma$ of $[n]$ with $\sigma(i) \ne i$ for all $i = 1, \dots, n$. Let $d_n$ denote the number of derangements of $[n]$. Then
--   $$d_n = \sum_{k=0}^{n} (-1)^k \binom{n}{k} (n-k)!.$$
--   For example $d_5 = 120 - 120 + 60 - 20 + 5 - 1 = 44$.
--
--   This is the answer to the hat-check problem and the starting point of the limit $d_n / n! \to 1/e$ (Theorem 7.12).
--
--   **Formalization Note.** $d_n$ is the cardinality of the subtype `{σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i}`, not Mathlib's `numDerangements` (which is defined by a recurrence) and not the sum itself. The identity is in $\mathbb Z$. The book says "for each positive integer $n$"; the statement is made for all $n \ge 0$, and at $n = 0$ both sides equal $1$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 147, Theorem 7.11

import Mathlib

namespace AppliedComb.InclExcl

/-- Theorem 7.11, Keller & Trotter p. 147: the number `d_n` of derangements of `[n]`
(permutations `σ` with `σ(i) ≠ i` for all `i`) satisfies
`d_n = ∑_{k=0}^{n} (-1)^k C(n, k) (n - k)!`. Stated for every `n ≥ 0`; the book says "each
positive integer `n`", and the case `n = 0` (`d_0 = 1`) also holds. -/
theorem derangements_count (n : ℕ) :
    (Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i : Fin n, σ i ≠ i} : ℤ) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k).factorial : ℤ) := by sorry

end AppliedComb.InclExcl
