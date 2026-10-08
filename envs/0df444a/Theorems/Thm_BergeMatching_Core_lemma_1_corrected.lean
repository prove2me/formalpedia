-- Prove2me | Theorems.Thm_BergeMatching_Core_lemma_1_corrected
-- name    : BergeMatching.Core.lemma_1_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:33:40.396145+00:00
-- url     : https://prove2.me/theorems/900612a4-fc15-4b7c-8e52-88eca79bd8c5
-- title:
--   Lemma 1 (corrected: neutral bases included in Y) — Gallai's lemma on components of the medium points
-- statement:
--   Let $G = (X, U)$ be a finite simple graph with a matching $V_0$, neutral points $N$, and $\bar G$, arrows and the classes $W$ (weak) and $M$ (medium) as in the definition of arrows. Let
--   $$
--   M^+ = M \cup \{\, n \in N : \text{some weak edge carries an arrow directed to } n \,\},
--   $$
--   and let $Y$ be the vertex set of a connected component of the subgraph of $G$ induced on $M^+$. If $\bar a$ is inaccessible (no arrow is directed to $\bar a$), then:
--   1. exactly one strong edge of $\bar G$ has exactly one endpoint in $Y$; it carries an arrow directed into $Y$ and none directed out of $Y$;
--   2. every weak edge of $G$ with exactly one endpoint in $Y$ carries an arrow directed out of $Y$ and none directed into $Y$;
--   3. every vertex not in $Y$ joined to $Y$ by an edge of $G$ is a weak point;
--   4. $$|Y| \ge 3 .$$
--
--   The paper attributes the lemma to T. Gallai. As printed, with $Y$ a component of $M$ alone, it is false: in the triangle on $\{0, 1, 2\}$ with $V_0 = \{01\}$, the only neutral point is $2$, $\bar a$ is inaccessible, the medium points are $0$ and $1$, so $Y = \{0, 1\}$ has $|Y| = 2$, its neighbour $2$ is neutral rather than weak, and no strong edge has exactly one endpoint in $Y$. The cause is the clause $x \notin N$ in the definition of medium points, which excludes a neutral base of a blossom; the corrected statement puts such bases into $Y$, with $\bar a n$ as the one strong edge entering $Y$.
--
--   **Formalization Note** This is a corrected form of the printed lemma, not the printed lemma. "Edges adjacent to $Y$" means edges with exactly one endpoint in $Y$, and "$\bar a$ is inaccessible" is read as "no arrow is directed to $\bar a$". Item 1 ranges over all strong edges of $\bar G$, including the edges $\bar a n$.
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), p. 843, Lemma 1 (T. Gallai), corrected

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_BergeMatching_Core_Arrows

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Lemma 1 (Gallai), in corrected form. The printed lemma takes `Y` to be
a component of the medium points and fails on a triangle with one matched edge; here `Y` is a
connected component of the subgraph induced on the medium points together with the neutral
points to which a weak edge is directed. If `ā` is inaccessible: exactly one strong edge of `Ḡ`
has exactly one endpoint in `Y`, it is directed into `Y` only; every weak edge of `G` with
exactly one endpoint in `Y` is directed out of `Y` only; every vertex outside `Y` joined to `Y`
by an edge is a weak point; and `|Y| ≥ 3`. -/
theorem lemma_1_corrected {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (Y : (G.induce {x : V | IsMedium G M x ∨
        (IsNeutral M x ∧ ∃ z, Arrow G M z (some x) ∧ s(z, some x) ∉ barStrong M)}).ConnectedComponent) :
    (∃ y w : Option V, y ∈ Option.some '' (Subtype.val '' Y.supp) ∧
        w ∉ Option.some '' (Subtype.val '' Y.supp) ∧
        s(w, y) ∈ barStrong M ∧ Arrow G M w y ∧ ¬ Arrow G M y w ∧
        ∀ y' w' : Option V, y' ∈ Option.some '' (Subtype.val '' Y.supp) →
          w' ∉ Option.some '' (Subtype.val '' Y.supp) → s(w', y') ∈ barStrong M →
            s(w', y') = s(w, y)) ∧
      (∀ y ∈ Subtype.val '' Y.supp, ∀ w : V, w ∉ Subtype.val '' Y.supp → G.Adj y w →
        s(y, w) ∉ M.edgeSet → Arrow G M (some y) (some w) ∧ ¬ Arrow G M (some w) (some y)) ∧
      (∀ w : V, w ∉ Subtype.val '' Y.supp → (∃ y ∈ Subtype.val '' Y.supp, G.Adj y w) →
        IsWeakPt G M w) ∧
      3 ≤ (Subtype.val '' Y.supp).ncard := by sorry

end BergeMatching.Core
