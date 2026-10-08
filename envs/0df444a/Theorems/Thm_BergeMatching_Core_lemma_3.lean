-- Prove2me | Theorems.Thm_BergeMatching_Core_lemma_3
-- name    : BergeMatching.Core.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:32:53.09178+00:00
-- url     : https://prove2.me/theorems/62fd3b0b-373b-4128-81da-1f877425c289
-- title:
--   Lemma 3 — with no medium and no inaccessible point, $S \cup N$, $W$ and $V_0$ are optimal
-- statement:
--   Let $G = (X, U)$ be a finite simple graph with a matching $V_0$, neutral points $N$, and classes $I$ (inaccessible), $W$ (weak), $S$ (strong) and $M$ (medium) defined by the arrows of $\bar G$. Assume that $\bar a$ is inaccessible (no arrow is directed to $\bar a$) and
--   $$
--   M = \emptyset, \qquad I = \emptyset .
--   $$
--   Then:
--   1. $S \cup N$ is a maximum internally stable set of $G$;
--   2. $W$ is a minimum cover of $G$;
--   3. $V_0$ is a maximum matching of $G$.
--
--   Here "maximum" and "minimum" refer to the number of elements. Lemma 3 settles the case of Theorem 1 in which no vertex is medium or inaccessible.
--
--   **Formalization Note** The medium class, written $M$ in the paper, is `IsMedium` in Lean, since `M` names the matching. "$\bar a$ is inaccessible" is read as "no arrow is directed to $\bar a$".
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), p. 843, Lemma 3

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_BergeMatching_Core_Arrows

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Lemma 3: if `ā` is inaccessible, `M = ∅` (no medium point) and
`I = ∅` (no inaccessible point), then `S ∪ N` is a maximum internally stable set, `W` is a
minimum cover, and `V₀` is a maximum matching. -/
theorem lemma_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (hMed : {x : V | IsMedium G M x} = ∅) (hI : {x : V | IsInaccessible G M x} = ∅) :
    IsMaximumIndepSet G ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x}) ∧
      IsMinimumVertexCover G {x : V | IsWeakPt G M x} ∧
      IsMaximumMatching M := by sorry

end BergeMatching.Core
