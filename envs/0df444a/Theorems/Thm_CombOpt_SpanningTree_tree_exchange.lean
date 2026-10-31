-- Prove2me | Theorems.Thm_CombOpt_SpanningTree_tree_exchange
-- name    : CombOpt.SpanningTree.tree_exchange
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:27.755993+00:00
-- url     : https://prove2.me/theorems/1193b9f3-5fa8-49a2-ae01-712f1622575c
-- title:
--   Lemma 2.7 — exchanging a tree-path edge for a non-tree edge gives a spanning tree
-- statement:
--   Let $T$ be the edge set of a spanning tree $H=(V,T)$ of $G$, let $e$ be an edge of $G$ not in $T$ with ends $v$ and $w$, and let $f$ be an edge of a simple path from $v$ to $w$ in $(V,T)$ (a path with distinct nodes using only edges of $T$). Then
--   $$H'=\bigl(V,\ (T\cup\{e\})\setminus\{f\}\bigr)$$
--   is a spanning tree of $G$.
--
--   This exchange step is the key to the proof of the cut property (Theorem 2.4).
--
--   **Formalization Note** If $e$ is a loop ($v=w$), the only simple path from $v$ to $v$ has no edges, so there is no $f$ and the statement is vacuous, as in the book.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Lemma 2.7, p. 13 (PDF p. 22)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree
import Definitions.Def_CombOpt_SpanningTree_Graph_Walk_support

namespace CombOpt.SpanningTree

/-- **Lemma 2.7: exchanging an edge of the tree path for the non-tree edge gives a spanning tree.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Lemma 2.7, p. 13 (PDF p. 22): "Let H = (V, T) be a spanning tree of G, let e = vw be an edge
of G but not H, and let f be an edge of a simple path in T from v to w. Then the subgraph
H′ = (V, (T ∪ {e})\{f}) is a spanning tree of G."

Let `T` be (the edge set of) a spanning tree, `e ∉ T` an edge with ends `v, w`, and `f` an edge of
a path from `v` to `w` with distinct nodes and all edges in `T`. Then `(T ∪ {e}) \ {f}` is a
spanning tree.

**Formalization Note.** "A simple path in T" is a path of `G` with pairwise distinct nodes
(`p.support.Nodup`) all of whose edges lie in `T`. If `e` is a loop (`v = w`) the only simple path
from `v` to `v` has no edges, so the statement is vacuous there, as in the book. -/
theorem tree_exchange {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Graph V E)
    (T : Finset E) (hT : G.IsSpanningTree T) (e : E) (v w : V) (he : G.ends e = s(v, w))
    (heT : e ∉ T) (f : E)
    (hf : ∃ p : G.Walk v w, p.support.Nodup ∧ (∀ g ∈ p.edges, g ∈ T) ∧ f ∈ p.edges) :
    G.IsSpanningTree ((insert e T).erase f) := by sorry

end CombOpt.SpanningTree
