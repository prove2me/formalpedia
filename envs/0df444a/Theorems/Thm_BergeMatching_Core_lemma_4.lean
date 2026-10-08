-- Prove2me | Theorems.Thm_BergeMatching_Core_lemma_4
-- name    : BergeMatching.Core.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:33:03.958984+00:00
-- url     : https://prove2.me/theorems/e1f54804-c291-4959-883f-6618a320049e
-- title:
--   Lemma 4 — a component of the inaccessible points has only weak, undirected edges leaving it
-- statement:
--   Let $G = (X, U)$ be a finite simple graph with a matching $V_0$, and let $I$ be the set of inaccessible points (non-neutral vertices at which no edge carries an arrow of $\bar G$). Let $Z$ be the vertex set of a connected component of the subgraph of $G$ induced on $I$. If $\bar a$ is inaccessible (no arrow is directed to $\bar a$), then:
--   1. every edge $zw$ with $z \in Z$ and $w \notin Z$ is weak and carries no arrow in either direction;
--   2. every vertex $w \notin Z$ joined to $Z$ by an edge is a weak point;
--   3. $$|Z| \ge 2 .$$
--
--   In Berge's proof of Theorem 1, Lemma 4 is what allows a component of $I$ to be shrunk to a single neutral vertex.
--
--   **Formalization Note** "Edges adjacent to $Z$" is read as edges with exactly one endpoint in $Z$: the strong edge at a vertex of $Z$ joins it to another vertex of $Z$, so edges with both endpoints in $Z$ cannot all be weak. "$\bar a$ is inaccessible" is read as "no arrow is directed to $\bar a$".
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), p. 843, Lemma 4

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_BergeMatching_Core_Arrows

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Lemma 4: let `Z` be a connected component of the subgraph induced
on the inaccessible points `I`; if `ā` is inaccessible, every edge with exactly one endpoint in
`Z` is weak and carries no arrow, every vertex outside `Z` joined to `Z` by an edge is a weak
point, and `|Z| ≥ 2`. -/
theorem lemma_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (Z : (G.induce {x : V | IsInaccessible G M x}).ConnectedComponent) :
    (∀ z ∈ Subtype.val '' Z.supp, ∀ w : V, w ∉ Subtype.val '' Z.supp → G.Adj z w →
        s(z, w) ∉ M.edgeSet ∧ ¬ Arrow G M (some z) (some w) ∧ ¬ Arrow G M (some w) (some z) ∧
          IsWeakPt G M w) ∧
      2 ≤ (Subtype.val '' Z.supp).ncard := by sorry

end BergeMatching.Core
