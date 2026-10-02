-- Prove2me | Theorems.Thm_AppliedComb_Graphs_interval_chromatic_eq_clique
-- name    : AppliedComb.Graphs.interval_chromatic_eq_clique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:04:26.412132+00:00
-- url     : https://prove2.me/theorems/e08a8fee-7806-4eb6-bae4-d7a29f7962d8
-- title:
--   Theorem 5.28 — interval graphs satisfy χ(G) = ω(G)
-- statement:
--   Let $G = (V, E)$ be a finite interval graph, the intersection graph of a family of closed real intervals indexed by $V$. Then
--   $$\chi(G) = \omega(G),$$
--   the chromatic number equals the clique number.
--
--   Since induced subgraphs of interval graphs are interval graphs, this shows interval graphs are perfect.
--
--   **Formalization Note.** $\chi(G)$ is Mathlib's `chromaticNumber` in $\mathbb N_\infty$ and $\omega(G)$ is Mathlib's `cliqueNum` in $\mathbb N$, cast to $\mathbb N_\infty$. On the empty graph both sides are $0$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 87, Theorem 5.28 (interval graph: p. 87)

import Mathlib
import Definitions.Def_AppliedComb_Graphs_IsIntervalGraph

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 87, Theorem 5.28. If `G = (V, E)` is a (finite) interval graph, then
`χ(G) = ω(G)`. -/
theorem interval_chromatic_eq_clique {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : IsIntervalGraph G) : G.chromaticNumber = (G.cliqueNum : ℕ∞) := by sorry

end AppliedComb.Graphs
