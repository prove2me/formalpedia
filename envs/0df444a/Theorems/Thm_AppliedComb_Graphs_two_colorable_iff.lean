-- Prove2me | Theorems.Thm_AppliedComb_Graphs_two_colorable_iff
-- name    : AppliedComb.Graphs.two_colorable_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:03:05.042107+00:00
-- url     : https://prove2.me/theorems/5a27eacf-0adb-4e33-b6e6-a28a15aa2eed
-- title:
--   Theorem 5.21 — a graph is 2-colorable iff it contains no odd cycle
-- statement:
--   Let $G$ be a finite graph and $\chi(G)$ its chromatic number, the least $t$ for which $G$ has a proper coloring with $t$ colors. Then
--   $$\chi(G) \le 2 \iff G \text{ contains no odd cycle},$$
--   where an odd cycle is a sequence $(x_1, \dots, x_n)$ of $n \ge 3$ distinct vertices, $n$ odd, with $x_i x_{i+1}$ an edge for $i < n$ and $x_1 x_n$ an edge.
--
--   This characterizes bipartite graphs and makes 2-colorability easy to recognize.
--
--   **Formalization Note.** $\chi(G)$ is Mathlib's `SimpleGraph.chromaticNumber` (valued in $\mathbb N_\infty$), which on a finite graph is the book's least number of colors. The obstruction is an odd *cycle* in the book's sense (distinct vertices), not an odd closed walk.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 82, Theorem 5.21 (2-colorable: p. 82; cycle: p. 71)

import Mathlib
import Definitions.Def_AppliedComb_Graphs_IsCycle

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 82, Theorem 5.21. A (finite) graph is 2-colorable, i.e. `χ(G) ≤ 2`, if
and only if it does not contain an odd cycle (a cycle of `n ≥ 3` distinct vertices with `n`
odd, p. 71). -/
theorem two_colorable_iff {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.chromaticNumber ≤ 2 ↔ ¬ ContainsOddCycle G := by sorry

end AppliedComb.Graphs
