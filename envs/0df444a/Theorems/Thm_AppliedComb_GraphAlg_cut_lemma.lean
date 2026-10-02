-- Prove2me | Theorems.Thm_AppliedComb_GraphAlg_cut_lemma
-- name    : AppliedComb.GraphAlg.cut_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:35:34.762811+00:00
-- url     : https://prove2.me/theorems/3fd01111-9bb9-44a3-8be5-6f4360d10c9d
-- title:
--   Lemma 12.6 — a lightest edge leaving a component lies in some optimal extension
-- statement:
--   Let $G = (V, E)$ be a finite connected graph with edge weights $w : E \to \mathbb{N}_0$. Let $F$ be a spanning forest of $G$, let $C$ be a connected component of $F$, and let $e = xy$ be an edge of $G$ of minimum weight among all edges of $G$ with one endpoint in $C$ and the other not in $C$. Then among all spanning trees of $G$ that contain the forest $F$ there is one of minimum weight that contains $e$:
--   $$\exists\, T \supseteq F \cup \{e\}\ \text{spanning tree of } G \ \text{ with } \ w(T) \le w(T') \ \text{ for every spanning tree } T' \supseteq F \text{ of } G.$$
--
--   This lemma is what makes greedy constructions of minimum weight spanning trees correct; the book derives the correctness of Kruskal's algorithm (Algorithm 12.8) and Prim's algorithm (Algorithm 12.10) from it.
--
--   **Formalization Note.** "Contains the forest $F$" is `F ≤ T` (every edge of $F$ is an edge of $T$). The edge $e = xy$ crosses $C$ in either orientation (`hcross`), and minimality is over every edge $uv$ of $G$ with $u \in C$, $v \notin C$ (by symmetry of edges this covers both orientations). Weights are `w : Sym2 V → ℕ`, used only on edges of $G$. Connectedness of $G$ is the standing assumption of Section 12.1 (p. 239). The page's remark "to avoid trivialities, we assume $n \ge 3$" is not imposed: the statement holds for every $n$, so omitting it is a (harmless) generalization.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 242, Lemma 12.6 (standing assumptions of Section 12.1, p. 239)

import Mathlib
import Definitions.Def_AppliedComb_GraphAlg_SpanningTree

namespace AppliedComb.GraphAlg

/-- Keller–Trotter, p. 242, Lemma 12.6. `G` is a connected graph with edge weights
`w : E → ℕ₀` (the standing assumptions of Section 12.1, p. 239). Let `F` be a spanning forest of
`G`, `C` a component of `F`, and `e = xy` an edge of minimum weight among all edges with one
endpoint in `C` and the other not in `C`. Then among all spanning trees of `G` that contain `F`
there is one of minimum weight that contains `e`. -/
theorem cut_lemma {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (w : Sym2 V → ℕ) (F : SimpleGraph V) (hF : IsSpanningForest G F)
    (C : F.ConnectedComponent) (x y : V) (hxy : G.Adj x y)
    (hcross : (x ∈ C.supp ∧ y ∉ C.supp) ∨ (y ∈ C.supp ∧ x ∉ C.supp))
    (hmin : ∀ u v : V, G.Adj u v → u ∈ C.supp → v ∉ C.supp → w s(x, y) ≤ w s(u, v)) :
    ∃ T : SimpleGraph V, IsSpanningTree G T ∧ F ≤ T ∧ T.Adj x y ∧
      ∀ T' : SimpleGraph V, IsSpanningTree G T' → F ≤ T' → weight w T ≤ weight w T' := by sorry

end AppliedComb.GraphAlg
