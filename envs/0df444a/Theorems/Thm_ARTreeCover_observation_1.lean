-- Prove2me | Theorems.Thm_ARTreeCover_observation_1
-- name    : ARTreeCover.observation_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:31.662348+00:00
-- url     : https://prove2.me/theorems/015d1ee1-a4a7-4c71-b988-c15fea7fa6fe
-- title:
--   Observation 1: from forest covers to tree covers
-- statement:
--   Let $F_1,\dots,F_m$ be a forest cover of a weighted graph $G$.
--
--   1. There is a family of forests, of unbounded size, each with at most one nontrivial component, which is a forest cover of $G$, such that for all $i,u,v$ some member $T'$ has $d_{T'}(u,v)\le d_{F_i}(u,v)$; it is spanning if every $F_i$ is.
--   2. There are trees $T_1,\dots,T_m$ on $V$ that form a forest cover of $G$ with $d_{T_i}(u,v)\le d_{F_i}(u,v)$ for all $i,u,v$.
--   3. If $G$ is connected and every $F_i$ is spanning, the $T_i$ of item 2 can be taken to be spanning trees of $G$.
--
--   The goal's connected clause follows from items 2 and 3, for the almost-Ramsey property as well as for the stretch.
--
--   Differences from the source:
--   - generalization: "with the same stretch" and "with equal or smaller stretch" → pointwise: d_{T_i} ≤ d_{F_i} for all pairs (min over the family in the first clause); reason: a pointwise bound implies the printed stretch claims on every instance, and it also preserves the almost-Ramsey property, which the printed form does not state and Theorem 19 uses
--   - encoding: a tree with V(T) ⊆ V in the set of all trees of the forests → a forest on all of V with at most one component containing an edge; reason: the other vertices are isolated; a one-vertex tree is the edgeless forest
--   - encoding: a tree cover T̄ with |T̄| = |F| → a tree on all of V, `Preconnected`, with one tree per index of the family; reason: on nonempty V this is `SimpleGraph.IsTree`; a family indexed by `Fin m` has size m with repetitions allowed
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: forests with V(F) ⊆ V and weights in (0, ∞] → a forest on all of V; a vertex outside V(F) is isolated; reason: this changes no distance between distinct vertices and gives d_F(u, u) = 0, which the paper assumes (p.31)
--   - reading: spanning: E(F) ⊆ E → every edge of F is an edge of G and carries G's weight; reason: a forest whose edges are edges of G but with other weights is not a subgraph of the weighted graph G
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Observation 1, p.29 (PDF p.32), cited from Elkin, Shabat, arXiv:2511.06263

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_IsForestCover

namespace ARTreeCover

/-- **Observation 1**, p.29 (PDF p.32), cited from [32]. Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let F be a forest cover of G = (V, E). The set T of all trees in the forests of F is a tree cover
with the same stretch as F (but not necessarily with the same size). If F is spanning, so is T. In
addition, there is a tree cover T̄, which is not necessarily spanning (even if F is spanning), with
equal or smaller stretch, such that |T̄| = |F|. Lastly, if G is a connected graph and F is spanning,
there is a spanning tree cover T̄span of G with |T̄span| = |F| and equal or smaller stretch as F."

Stated pointwise. First sentence: a family `T'` of unbounded size in which every member has at most
one nontrivial component, dominating `G`, with `min_j d_{T'_j} ≤ d_{F_i}` for every `i`, spanning if
every `F_i` is. Second and third sentences: from `F₁, …, F_m` there are trees `T₁, …, T_m` on `V`
forming a forest cover with `d_{T_i} ≤ d_{F_i}` everywhere; if `G` is connected and every `F_i` is
spanning, every `T_i` is a spanning tree of `G`.

**Formalization Note.**
1. In the second and third sentences a tree is a `WForest` whose graph is preconnected (on nonempty
   `V` this is `SimpleGraph.IsTree`; on empty `V` it holds vacuously).
2. In the first sentence a tree with `V(T) ⊆ V` is a `WForest` on all of `V` with at most one
   component containing an edge; the other vertices are isolated. A one-vertex tree is the edgeless
   forest.
3. The pointwise bounds imply "the same stretch" and "equal or smaller stretch", and they also
   preserve the almost-Ramsey property, which Theorem 19 uses. -/
theorem observation_1 {V : Type} [Fintype V] (G : WGraph V) (m : ℕ) (F : Fin m → WForest V)
    (hF : IsForestCover G F) :
    (∃ (m' : ℕ) (T' : Fin m' → WForest V),
      (∀ j a b c d, (T' j).graph.Adj a b → (T' j).graph.Adj c d → (T' j).graph.Reachable a c) ∧
      IsForestCover G T' ∧
      (∀ i u v, ∃ j, (T' j).dist u v ≤ (F i).dist u v) ∧
      ((∀ i, (F i).IsSpanning G) → ∀ j, (T' j).IsSpanning G)) ∧
    ∃ T : Fin m → WForest V,
      (∀ i, (T i).graph.Preconnected) ∧ IsForestCover G T ∧
      (∀ i u v, (T i).dist u v ≤ (F i).dist u v) ∧
      (G.graph.Connected → (∀ i, (F i).IsSpanning G) → ∀ i, (T i).IsSpanning G) := by sorry

end ARTreeCover
