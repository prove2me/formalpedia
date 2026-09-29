-- Prove2me | Theorems.Thm_DreyfusWagner_Steiner_steinerTree_isAcyclic
-- name    : DreyfusWagner.Steiner.steinerTree_isAcyclic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:04:35.256+00:00
-- url     : https://prove2.me/theorems/10c5a0f4-33b7-4711-8240-08b752a72375
-- title:
--   §1, p. 197 — a Steiner path contains no cycles
-- statement:
--   Let $G = (N, A)$ be a finite connected undirected graph whose arcs have positive lengths $|a| > 0$, and let $Y \subseteq N$. If $S \subseteq A$ is a Steiner path connecting $Y$ — a set of arcs connecting all members of $Y$ with minimum total length — then
--   $$S \text{ contains no cycle, i.e. } S \text{ is a forest.}$$
--
--   This is the "easily proven fact" with which Dreyfus and Wagner open their analysis: a minimum connecting arc set is a tree. It is what lets one speak of branches, junction nodes and subtrees of a Steiner path in the Optimal Decomposition Theorem.
--
--   **Formalization Note** "Contains no cycle" is `IsAcyclic` for the graph whose edges are the arcs of $S$. Positivity of the arc lengths is essential: with an arc of length zero a minimum connecting set may contain a cycle. Connectivity of $G$ is the paper's standing assumption and is kept as a hypothesis.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 197, §1, first paragraph

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, §1, p. 197: a Steiner path `S` must be a tree, i.e. it contains no
cycles. -/
theorem steinerTree_isAcyclic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (S : Finset (Sym2 V)) (hS : IsSteinerTree G ℓ Y S) :
    (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).IsAcyclic := by sorry

end DreyfusWagner.Steiner
