-- Prove2me | Theorems.Thm_AppliedComb_Ramsey_ramsey_theorem
-- name    : AppliedComb.Ramsey.ramsey_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:19:10.40515+00:00
-- url     : https://prove2.me/theorems/bbe513a4-b0a7-4002-9a7d-32bf5c0cf65f
-- title:
--   Theorem 11.2 — Ramsey's Theorem for Graphs
-- statement:
--   Let $m$ and $n$ be positive integers. Then there exists a least positive integer $R(m, n)$ such that every finite simple graph $G$ with at least $R(m, n)$ vertices contains a complete subgraph on $m$ vertices or an independent set of size $n$. In other words, the set
--   $$\{N \ge 1 : \text{every graph with at least } N \text{ vertices has an } m\text{-clique or an independent set of size } n\}$$
--   is nonempty, and its least element is the Ramsey number $R(m, n)$.
--
--   This is the graph case of Ramsey's theorem: in every sufficiently large graph, a large "boring" induced subgraph (complete or edgeless) is unavoidable. The numbers $R(m, n)$ are the subject of the rest of the chapter.
--
--   **Formalization Note.** The statement is `IsLeast {N | 0 < N ∧ IsRamseyBound m n N} (ramseyNumber m n)`, with `IsRamseyBound` and `ramseyNumber` from the definition `AppliedComb.Ramsey.ramseyNumber`. Its content is that the set is nonempty (then `ramseyNumber`, defined as its `sInf`, is its least element). The explicit bound from the book's proof is the separate item `AppliedComb.Ramsey.ramsey_le_choose`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 230, Theorem 11.2

import Mathlib
import Definitions.Def_AppliedComb_Ramsey_ramseyNumber

namespace AppliedComb.Ramsey

/-- Theorem 11.2 (Ramsey's Theorem for Graphs), Keller & Trotter p. 230: for positive integers
`m, n` there is a least positive integer `R(m, n)` such that every graph with at least `R(m, n)`
vertices contains an `m`-clique or an independent set of size `n`; `ramseyNumber m n` is it. -/
theorem ramsey_theorem (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsLeast {N : ℕ | 0 < N ∧ IsRamseyBound m n N} (ramseyNumber m n) := by sorry

end AppliedComb.Ramsey
