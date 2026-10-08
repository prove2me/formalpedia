-- Prove2me | Theorems.Thm_BergeMatching_Core_lemma_2
-- name    : BergeMatching.Core.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:32:50.55105+00:00
-- url     : https://prove2.me/theorems/1a08491b-29cb-4dd8-b3c2-44661ed81fbe
-- title:
--   Lemma 2 — if $\bar a$ is inaccessible, $S \cup N$ is internally stable
-- statement:
--   Let $G = (X, U)$ be a finite simple graph with a matching $V_0$, let $\bar G$ be $G$ with an extra vertex $\bar a$ joined by strong edges to the neutral points $N$, and label the vertices by the arrows of alternating chains from $\bar a$ (as in the definition of the classes $I$, $W$, $S$ and the medium points). If $\bar a$ is inaccessible, that is, no arrow is directed to $\bar a$, then
--   $$
--   S \cup N \ \text{is internally stable},
--   $$
--   i.e. no edge of $G$ joins two vertices of $S \cup N$, where $S$ is the set of strong points.
--
--   Together with Lemma 3 this gives the certificate of maximality in the case where there are no medium and no inaccessible points.
--
--   **Formalization Note** "$\bar a$ is inaccessible" is read as "no arrow is directed to $\bar a$"; see the definition of arrows.
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), p. 843, Lemma 2

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_BergeMatching_Core_Arrows

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Lemma 2: if `ā` is inaccessible, `S ∪ N` is internally stable. -/
theorem lemma_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M) :
    G.IsIndepSet ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x}) := by sorry

end BergeMatching.Core
