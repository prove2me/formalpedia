-- Prove2me | Theorems.Thm_CombOpt_MatroidPolytope_matchingIndep_isMatroid
-- name    : CombOpt.MatroidPolytope.matchingIndep_isMatroid
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:49.05124+00:00
-- url     : https://prove2.me/theorems/f07c3214-3430-481c-9055-154229c3032c
-- title:
--   Proposition 8.1 — the node sets covered by matchings form a matroid
-- statement:
--   Let $G=(V,E)$ be a finite graph (loops and parallel edges allowed), let $S=V$, and let $\mathcal I$ be the family of sets $J\subseteq V$ for which some matching of $G$ covers every node of $J$. Then $(S,\mathcal I)$ is a matroid: it satisfies (M0), (M1) and (M2).
--
--   This is the **matching matroid**: although the matchings of a graph do not form a matroid, the sets of nodes they can cover do.
--
--   Differences from the source:
--   - reading: a matching is "a set M of edges such that no node of G is incident with more than one edge in M" (p. 127) → a set of non-loop edges, two distinct of which share no end; reason: the same page says a matching covers exactly 2|M| nodes, which excludes loops (the series-wide reading in paper.md)
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 8.1, p. 276 (PDF p. 283)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_Graph_matchingIndep

namespace CombOpt.MatroidPolytope

/-- **Proposition 8.1: the matching matroid.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 8.1, p. 276 (PDF p. 283): "Let G = (V, E) be a graph, let S = V, and let
I = {J ⊆ S : there is a matching M′ of G covering all the elements of J}. … Proposition 8.1
M = (S, I) defined above is a matroid."

For every finite graph `G` (loops and parallel edges allowed), the family of node sets covered by
some matching satisfies (M0), (M1) and (M2).

**Formalization Note.** Matchings contain no loops (p. 127); a matching may cover nodes outside
`J`. -/
theorem matchingIndep_isMatroid {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E) :
    IsMatroid G.matchingIndep := by sorry

end CombOpt.MatroidPolytope
