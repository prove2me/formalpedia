-- Prove2me | Theorems.Thm_DreyfusWagner_Steiner_steinerLength_pair_eq_pathDist
-- name    : DreyfusWagner.Steiner.steinerLength_pair_eq_pathDist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:04:59.285873+00:00
-- url     : https://prove2.me/theorems/3f30b1cf-6ad0-4515-8733-215b5288d1a9
-- title:
--   Appendix A, p. 205 — the Steiner path connecting two nodes is the shortest path
-- statement:
--   Let $G = (N, A)$ be a finite connected undirected graph whose arcs have positive lengths, and let $i, j \in N$. Then the Steiner length of the two-node set $\{i, j\}$ equals the shortest-path length between them:
--   $$\operatorname{St}(\{i, j\}) = D(i, j).$$
--   For $i = j$ both sides are $0$.
--
--   This is the base case of the Dreyfus–Wagner recursion: line (3) of Algorithm A initialises the table on singletons $\{t\}$ with the shortest-path lengths $D(t, J)$, which are the Steiner lengths of the pairs $\{t, J\}$.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 205, Appendix A, second paragraph (last two sentences before 'First we insert some definitions')

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, Appendix A, p. 205: the Steiner path connecting two nodes is the
shortest path between them, so its length is `D(i,j)`. -/
theorem steinerLength_pair_eq_pathDist {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected) (i j : V) :
    steinerLength G ℓ {i, j} = pathDist G ℓ i j := by sorry

end DreyfusWagner.Steiner
