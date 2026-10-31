-- Prove2me | Theorems.Thm_CombOpt_SpanningTree_cut_property
-- name    : CombOpt.SpanningTree.cut_property
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:06.860129+00:00
-- url     : https://prove2.me/theorems/814bd3a8-c08f-4ecf-8a1d-76b20595a422
-- title:
--   Theorem 2.4 — the cut property: a minimum-cost edge of a cut avoiding $B$ keeps $B$ extendible to an MST
-- statement:
--   Let $c\in\mathbb R^E$ be edge costs. Call $A\subseteq E$ **extendible to an MST** if $A$ is contained in the edge set of some MST of $G$.
--
--   Suppose that $B\subseteq E$ is extendible to an MST, and that $e$ is a minimum-cost edge of some cut $D=\delta(A)$ (that is, $e\in D$ and $c_e\le c_f$ for all $f\in D$) satisfying $D\cap B=\emptyset$. Then $B\cup\{e\}$ is extendible to an MST.
--
--   Both Kruskal's and Prim's algorithms are proved correct by repeated application of this theorem.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 2.4, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsMST
import Definitions.Def_CombOpt_SpanningTree_Graph_cut

namespace CombOpt.SpanningTree

/-- **Theorem 2.4: adding a minimum-cost edge of a cut disjoint from B keeps B extendible to an
MST.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 2.4, p. 12 (PDF p. 21): "Suppose that B ⊆ E, that B is extendible to an MST, and
that e is a minimum-cost edge of some cut D satisfying D ∩ B = ∅. Then B ∪ {e} is extendible to an
MST", where "a subset A of edges of G [is] extendible to an MST if A is contained in the edge-set
of some MST of G".

Let `c` be real edge costs and `B` a set of edges contained in some MST. Let `D = δ(A)` be a cut
with `D ∩ B = ∅`, and let `e ∈ D` satisfy `c e ≤ c f` for all `f ∈ D`. Then `B ∪ {e}` is contained
in some MST.

**Formalization Note.** "Extendible to an MST" is written out as `∃ T, G.IsMST c T ∧ B ⊆ T`.
A cut is `δ(A)` for an arbitrary node set `A` (p. 12); since `e ∈ δ(A)`, `A` is automatically a
proper nonempty node set. -/
theorem cut_property {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Graph V E)
    (c : E → ℝ) (B : Finset E) (hB : ∃ T : Finset E, G.IsMST c T ∧ B ⊆ T) (e : E)
    (he : ∃ A : Finset V, e ∈ G.cut A ∧ (∀ f ∈ G.cut A, c e ≤ c f) ∧ Disjoint (G.cut A) B) :
    ∃ T : Finset E, G.IsMST c T ∧ insert e B ⊆ T := by sorry

end CombOpt.SpanningTree
