-- Prove2me | Theorems.Thm_BoundedDegreeST_LowerUpper_lemma_5_3
-- name    : BoundedDegreeST.LowerUpper.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:39.635811+00:00
-- url     : https://prove2.me/theorems/200578c1-7e60-44f6-855b-a4f500204a79
-- title:
--   Lemma 5.3 — a basic solution is the unique solution of a laminar family of tight sets and tight lower/upper degree rows
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $F$ a forest on $V$ edge-disjoint from $E$ that is not a spanning tree, and $x^*$ a basic feasible solution of LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ with support $E^*$. Then there are $T_U\subseteq U$, $T_W\subseteq W$ and a nonempty laminar family $\mathcal L\subseteq\mathcal I(F)$ of nonempty sets such that $x^*$ restricted to $E^*$ is the unique solution in $\mathbb R^{E^*}$ of
--
--   $$
--   x(\delta(v))=A_v\ (v\in T_U),\qquad x(\delta(v))=B_v\ (v\in T_W),\qquad x(E(S))=|S|-|F(S)|-1\ (S\in\mathcal L),
--   $$
--
--   the vectors $\{\chi_{E(S)}:S\in\mathcal L\}\cup\{\chi_{\delta(v)}:v\in T_U\}\cup\{\chi_{\delta(v)}:v\in T_W\}$ are linearly independent, and $|E^*|=|\mathcal L|+|T_U|+|T_W|$.
--
--   This is the structural description of extreme points on which the counting argument of §5.1 rests.
--
--   **Formalization Note** The hypothesis that $F$ is not a spanning tree is implicit in the paper (the lemma is applied after Step 1 has not returned); without it $E^*=\varnothing$ and no nonempty $\mathcal L$ need exist. The vectors live in $\mathbb R^{E^*}$ and are indexed by $\mathcal L\sqcup T_U\sqcup T_W$.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 668, Lemma 5.3

import Definitions.Def_BoundedDegreeST_LowerUpper_LP

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Lemma 5.3, p. 668: a basic feasible solution of
LP-MBDCT(G, 𝓐, 𝓑, U, W, F) is the unique solution of a linearly independent
system of tight rows given by `T_U ⊆ U`, `T_W ⊆ W` and a nonempty laminar
family `𝓛 ⊆ 𝓘(F)`, with `|E*| = |𝓛| + |T_U| + |T_W|`. The hypothesis that `F`
is not a spanning tree is implicit in the paper (Step 1 has not returned). -/
theorem lemma_5_3 {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V) (x : Sym2 V → ℝ)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F) :
    ∃ (TU TW : Finset V) (L : Finset (Finset V)),
      DefinesBasis E A B U W F x L TU TW := by sorry

end BoundedDegreeST.LowerUpper
