-- Prove2me | Theorems.Thm_ChvatalPolytopes_SeriesParallel_dirac_two_vertices_degree_le_two
-- name    : ChvatalPolytopes.SeriesParallel.dirac_two_vertices_degree_le_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:25:27.535515+00:00
-- url     : https://prove2.me/theorems/38f92135-c51b-4fb4-ba84-ddf18268fd11
-- title:
--   Dirac: a series-parallel network has two vertices of degree at most two
-- statement:
--   Let $G=(V,E)$ be a series-parallel network, i.e. a finite graph containing no homeomorph of $K_4$, with at least two vertices. Then there are two distinct vertices $a\ne b$ with
--   $$
--   d(a)\le 2\qquad\text{and}\qquad d(b)\le 2 .
--   $$
--
--   This result of Dirac is what lets the proof of Theorem 7.1 pick a vertex of degree at most two and reduce the graph.
--
--   **Formalization Note** The hypothesis $|V|\ge2$ is made explicit: as printed ("every series-parallel network includes at least two vertices of degree at most two") the statement fails for the one-vertex graph and the empty graph. Degrees are Mathlib's `SimpleGraph.degree`.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 150, §7 (Dirac [6, Satz 5])

import Mathlib
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel

namespace ChvatalPolytopes.SeriesParallel

/-- Dirac's theorem (cited in Chvátal 1975, p. 150, as [6, Satz 5]): every series-parallel network
includes at least two vertices of degree at most two.

The hypothesis `2 ≤ |V|` is made explicit: as printed the statement fails for the graph with one
vertex (and for the empty graph), which has fewer than two vertices at all. -/
theorem dirac_two_vertices_degree_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G)
    (hV : 2 ≤ Fintype.card V) :
    ∃ a b : V, a ≠ b ∧ G.degree a ≤ 2 ∧ G.degree b ≤ 2 := by sorry

end ChvatalPolytopes.SeriesParallel
