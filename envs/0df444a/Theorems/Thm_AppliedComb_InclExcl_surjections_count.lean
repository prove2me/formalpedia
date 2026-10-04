-- Prove2me | Theorems.Thm_AppliedComb_InclExcl_surjections_count
-- name    : AppliedComb.InclExcl.surjections_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:10:38.456374+00:00
-- url     : https://prove2.me/theorems/0f9e8b3c-b985-49b2-a87b-2fb81c828b56
-- title:
--   Theorem 7.9 — The number of surjections from [n] to [m]
-- statement:
--   For integers $n, m \ge 0$, let $S(n, m)$ denote the number of **surjections** from $[n] = \{1, \dots, n\}$ to $[m] = \{1, \dots, m\}$, that is, functions $f : [n] \to [m]$ such that every element of $[m]$ is $f(j)$ for some $j$. Then
--   $$S(n, m) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (m-k)^n.$$
--   For example $S(5, 3) = 243 - 96 + 3 - 0 = 150$, and $S(n, m) = 0$ when $n < m$.
--
--   The formula counts the ways to distribute $n$ distinguishable objects among $m$ distinct recipients so that every recipient gets at least one; it is the main application of the Principle of Inclusion-Exclusion in the chapter.
--
--   **Formalization Note.** $S(n, m)$ is the cardinality of the subtype `{f : Fin n → Fin m // Function.Surjective f}`; it is not defined by the formula and not via `Nat.stirlingSecond` (which counts partitions, i.e. surjections up to relabelling the codomain, and differs by the factor $m!$). The identity is stated in $\mathbb Z$, with $(m - k)$ computed in $\mathbb N$ for $0 \le k \le m$ and cast. The book introduces $S(n, m)$ for positive $n, m$; the statement is made for all $n, m \ge 0$, with Lean's convention $0^0 = 1$ (so $S(0,0) = 1$ and $S(0, m) = 0$ for $m \ge 1$, matching the formula).
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 146, Theorem 7.9

import Mathlib

namespace AppliedComb.InclExcl

/-- Theorem 7.9, Keller & Trotter p. 146: the number `S(n, m)` of surjections from `[n]` to
`[m]` (here from `Fin n` onto `Fin m`) is `∑_{k=0}^{m} (-1)^k C(m, k) (m - k)^n`. Stated for all
`n, m ≥ 0` (the book says "positive integers"), with Lean's `0 ^ 0 = 1`. -/
theorem surjections_count (n m : ℕ) :
    (Fintype.card {f : Fin n → Fin m // Function.Surjective f} : ℤ) =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ k * (m.choose k : ℤ) * ((m - k : ℕ) : ℤ) ^ n := by sorry

end AppliedComb.InclExcl
