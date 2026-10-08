-- Prove2me | Theorems.Thm_BoundedDegreeST_LowerUpper_lemma_5_1
-- name    : BoundedDegreeST.LowerUpper.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:09.968125+00:00
-- url     : https://prove2.me/theorems/6352cff2-445e-496e-b8be-3a8c74018e87
-- title:
--   Lemma 5.1 — a basic solution has an edge with x*_e = 1 or a vertex v ∈ U ∪ W with deg_{E*}(v) = 2
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $F$ a forest on $V$ edge-disjoint from $E$ that is not a spanning tree, and $x^*$ a basic feasible solution of LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ with support $E^*$. Then at least one of the following holds:
--
--   1. there is an edge $e$ with $x^*_e=1$;
--   2. there is a vertex $v\in U\cup W$ with $\deg_{E^*}(v)=2$.
--
--   $$
--   (\exists e\in E:\ x^*_e=1)\ \ \lor\ \ (\exists v\in U\cup W:\ \deg_{E^*}(v)=2).
--   $$
--
--   This is the key lemma that makes every iteration of MBDCT Algorithm 2 progress: it either fixes an edge or removes a degree constraint.
--
--   **Formalization Note** The hypothesis that $F$ is not a spanning tree is implicit in the paper (Step 1 has not returned). Degree bounds are integers.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 668, Lemma 5.1

import Definitions.Def_BoundedDegreeST_LowerUpper_LP

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Lemma 5.1, p. 668: a basic feasible solution `x*` of
LP-MBDCT(G, 𝓐, 𝓑, U, W, F) with support `E*` has an edge `e` with `x*_e = 1`,
or a vertex `v ∈ U ∪ W` with `deg_{E*}(v) = 2`. The hypothesis that `F` is not
a spanning tree is implicit in the paper (Step 1 has not returned). -/
theorem lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V) (x : Sym2 V → ℝ)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F) :
    (∃ e ∈ E, x e = 1) ∨ (∃ v ∈ U ∪ W, degree (support E x) v = 2) := by sorry

end BoundedDegreeST.LowerUpper
