-- Prove2me | Theorems.Thm_BimatrixStableSet_theorem_5
-- name    : BimatrixStableSet.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:52.473845+00:00
-- url     : https://prove2.me/theorems/d5792251-dd8c-4729-bd71-1d6ffdcc6d75
-- title:
--   Theorem 5 — any non-degenerate $5\times5$ game has at most 31 Nash equilibria
-- statement:
--   Let $A,B\in\mathbb R^{5\times5}$, and let the bimatrix game $(A,B)$ be non-degenerate. Then the set of Nash equilibria of $(A,B)$, that is, of pairs of mixed strategies that are mutual best responses, has at most
--
--   $$
--   31
--   $$
--
--   elements.
--
--   This settles the case $n=5$ of the conjecture of Quint and Shubik that a non-degenerate $n\times n$ game has at most $2^n-1$ Nash equilibria. The conjecture was known for $n\le4$ and to fail for $n\ge6$.
--
--   Differences from the source:
--   - encoding: "at most $c$ equilibria" → `Set.encard` $\le c$ in $\mathbb N_\infty$; reason: finiteness is part of the claim, so no count of an infinite set collapses
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Theorem 5, p.13

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_BimatrixStableSet_BestResponse

open RankOneBimatrix.BinSearch

namespace BimatrixStableSet

/-- Theorem 5, p.13 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): any non-degenerate
`5 × 5` game has at most 31 Nash equilibria.

**Formalization Note.** Nash equilibria are the mixed-strategy pairs of `IsNE`, so `(0, 0)` is not
counted. The entries of `A` and `B` are arbitrary reals: neither positivity nor boundedness of the
best-response polyhedra is assumed, since adding a constant to a payoff matrix changes no best
response (p.6). `Set.encard` counts in `ℕ∞`, so finiteness of the set is part of the claim. -/
theorem theorem_5 (A B : Matrix (Fin 5) (Fin 5) ℝ) (hAB : IsNondegenerate A B) :
    {p : (Fin 5 → ℝ) × (Fin 5 → ℝ) | IsNE A B p.1 p.2}.encard ≤ 31 := by sorry

end BimatrixStableSet
