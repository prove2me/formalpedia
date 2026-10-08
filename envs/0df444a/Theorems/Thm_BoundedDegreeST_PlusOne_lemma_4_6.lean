-- Prove2me | Theorems.Thm_BoundedDegreeST_PlusOne_lemma_4_6
-- name    : BoundedDegreeST.PlusOne.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:38.814261+00:00
-- url     : https://prove2.me/theorems/9a66610e-e607-4bfc-a8e1-f61d621964c1
-- title:
--   Lemma 4.6 — token bound for each laminar subtree
-- statement:
--   In the contradiction setting of Lemma 4.1, let $(\mathcal L,T)$ be the laminar basis of a basic feasible solution with support $E^*$. No supported edge has value $1$, and every $w\in W$ has $\deg_{E^*}(w)>B_w+1$. For every root $S\in\mathcal L$, the tokens initially attached to vertices in $S$ suffice to give two tokens to each vertex of $T\cap S$, two to each strict descendant of $S$ in $\mathcal L$, and four to $S$ itself. Numerically,
--
--   $$
--   \sum_{v\in S}\deg_{E^*}(v)\ge 2|T\cap S|+2|\{R\in\mathcal L:R\subsetneq S\}|+4.
--   $$
--
--   This is the counting statement used to contradict the basis cardinality in Lemma 4.1.
--
--   **Formalization Note** The Lean conclusion is the numerical token inequality that the source's distribution entails. All surrounding contradiction hypotheses are explicit.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 667, Lemma 4.6

import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Lemma 4.6, p. 667, as the numerical token-distribution bound. -/
theorem lemma_4_6 {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (S : Finset V)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F)
    (hbasis : DefinesBasis I.E I.B I.W I.F x L T)
    (hnoone : ∀ e ∈ support I.E x, x e ≠ 1)
    (hnosmall : ∀ w ∈ I.W, (degree (support I.E x) w : ℤ) > I.B w + 1)
    (hroot : S ∈ L) :
    2 * (T ∩ S).card +
      2 * (L.filter (fun R => R ⊂ S)).card + 4 ≤
      ∑ v ∈ S, degree (support I.E x) v := by sorry
end BoundedDegreeST.PlusOne
