-- Prove2me | Theorems.Thm_DreyfusWagner_Steiner_theorem1_branch_isSteinerTree
-- name    : DreyfusWagner.Steiner.theorem1_branch_isSteinerTree
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:05:38.398242+00:00
-- url     : https://prove2.me/theorems/efabead1-8006-4c72-80cd-c71629bd15e1
-- title:
--   Theorem 1 — the branch of a Steiner tree through $C \subseteq B(x)$ is a Steiner tree for $Y_C(x) \cup \{x\}$
-- statement:
--   Let $G = (N, A)$ be a finite connected undirected graph whose arcs have positive lengths, let $Y \subseteq N$, and let $S$ be a Steiner tree connecting $Y$. Let $x$ be a node touching an arc of $S$, let $B(x)$ be the set of arcs of $S$ touching $x$, and let $C \subseteq B(x)$. Let $Y_C(x)$ be the set of nodes of $Y$ reachable from $x$ along paths in $S$ whose first arc lies in $C$, and put $Y_C = Y_C(x) \cup \{x\}$. Then
--
--   $$\text{the arcs of } S \text{ involved in connecting the nodes of } Y_C \text{ form a Steiner tree connecting } Y_C.$$
--
--   In words: cutting a Steiner tree at any of its nodes and keeping the branches through a chosen set of arcs at that node gives an optimal Steiner tree for the terminals on those branches together with the cut node. Dreyfus and Wagner use this to view Steiner trees as collections of optimal subtrees joined at their roots, which is the first half of the proof of the Optimal Decomposition Theorem.
--
--   **Formalization Note** "The arcs of $S$ involved in connecting the nodes of $Y_C$" is read as the set of arcs of $S$ lying on some path in $S$ from $x$ to a node of $Y_C(x)$ (see the definition of the branch). The paper writes $C \subset B(x)$ for a not necessarily proper subset; the statement uses $C \subseteq B(x)$, so $C = \emptyset$ (branch empty, $Y_C = \{x\}$) and $C = B(x)$ are included.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 206, Appendix A, Theorem 1 (definitions on p. 205)

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem
import Definitions.Def_DreyfusWagner_Steiner_Branch

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, Appendix A, Theorem 1, p. 206: for a Steiner tree `S` connecting `Y`, a
node `x` touching an arc of `S` and a set `C ⊆ B(x)` of arcs of `S` at `x`, the arcs of `S`
involved in connecting `Y_C = Y_C(x) ∪ {x}` form a Steiner tree connecting `Y_C`. -/
theorem theorem1_branch_isSteinerTree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (S : Finset (Sym2 V)) (hS : IsSteinerTree G ℓ Y S)
    (x : V) (hx : ∃ e ∈ S, x ∈ e) (C : Finset (Sym2 V)) (hC : C ⊆ touchingArcs S x) :
    IsSteinerTree G ℓ (insert x (reachVia Y S x C)) (branchArcs Y S x C) := by sorry

end DreyfusWagner.Steiner
