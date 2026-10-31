-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_eq_6_9
-- name    : CombOpt.MatchingPolytope.eq_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:17.556004+00:00
-- url     : https://prove2.me/theorems/a4174bc6-6ff1-49b5-a49b-6cf23643ab24
-- title:
--   (6.9) — in the blossom case every tight matching satisfies $x(\gamma(S))=(|S|-1)/2$ (corrected: loopless)
-- statement:
--   Let $G=(V,E)$ be a graph without loops and let $M(G)\subseteq\mathbb R^E$ be its matching polytope. Let $w\in\mathbb R^E$ and $t\in\mathbb R$ be such that the inequality
--   $$w^\top x\le t \qquad (6.8)$$
--   is valid for $M(G)$ and induces a facet of $M(G)$, and let $\mathcal M^*$ be the set of matchings $M$ of $G$ with $w^\top\chi_M=t$. Suppose that
--
--   1. $w_e\ge0$ for all $e\in E$, and
--   2. for each node $v\in V$ some matching in $\mathcal M^*$ misses $v$ (no edge of it has $v$ as an end).
--
--   Let $S$ be the node set of the graph $G'$ formed by the edges $e$ with $w_e>0$, i.e. the set of ends of such edges. Then every matching $M\in\mathcal M^*$ satisfies
--   $$\chi_M(\gamma(S))=|M\cap\gamma(S)|=\frac{|S|-1}{2}. \qquad (6.9)$$
--
--   This is the last case of the facet argument in the proof of the Matching Polytope Theorem: it shows that the blossom inequality for $S$ induces the same facet as (6.8).
--
--   Differences from the source:
--   - correction: a graph $G$ (loops allowed) → $G$ loopless; reason: counterexample: a triangle $abc$ and a further node $d$ with a loop $\ell$, $w=1$ on all four edges, $t=1$; no matching contains $\ell$ (p. 127), so $x_\ell=0$ on $M(G)$, $w^\top x\le1$ induces the facet $x_{ab}+x_{bc}+x_{ca}=1$ and every node is missed by a matching in $\mathcal M^*$, but $S=\{a,b,c,d\}$ and $M=\{ab\}$ gives $1\ne3/2$
--   - reading: "$w^\top x\le t$ (6.8) induces a facet of $M(G)$" → (6.8) is valid for $M(G)$ and $\{x\in M(G): w^\top x=t\}$ is a facet; reason: the proof uses validity (removing an edge with $w_e<0$ "would violate (6.8)"); without it $w\ge0$ with $w^\top x\ge t$ valid gives counterexamples
--   - reading: "the other faces" are proper faces (p. 204) → a proper face is a face different from $\emptyset$ and from $P$; reason: the literal reading of the sentence; with $\emptyset$ proper, $\emptyset$ would be a facet of $\mathbb R^n$ and Corollary 6.19 would fail for the empty system
--   - encoding: conv.hull$(S)$ of a finite set, the set of convex combinations of $S$ (p. 199) → Mathlib's `convexHull ℝ S`; reason: for a finite set both are the set of convex combinations of finitely many points of $S$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, proof of Theorem 6.20, pp. 214–215 (PDF pp. 222–223), equation (6.9)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsMatching
import Definitions.Def_CombOpt_MatchingPolytope_charVec
import Definitions.Def_CombOpt_MatchingPolytope_Graph_matchingPolytope
import Definitions.Def_CombOpt_MatchingPolytope_Graph_cut
import Definitions.Def_CombOpt_MatchingPolytope_Graph_gamma
import Definitions.Def_CombOpt_MatchingPolytope_Graph_system67
import Definitions.Def_CombOpt_MatchingPolytope_IsValid
import Definitions.Def_CombOpt_MatchingPolytope_IsSupportingHyperplane
import Definitions.Def_CombOpt_MatchingPolytope_IsFace
import Definitions.Def_CombOpt_MatchingPolytope_IsProperFace
import Definitions.Def_CombOpt_MatchingPolytope_IsFacet
import Definitions.Def_CombOpt_MatchingPolytope_inducedFace

namespace CombOpt.MatchingPolytope

/-- **(6.9), the blossom case of the proof of the Matching Polytope Theorem** —
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, pp. 214–215 (PDF pp. 222–223): "Suppose w^T x ≤ t (6.8) induces a facet of M(G) and
let M* denote the set of matchings for which (6.8) holds as an equation. … Finally, suppose
w_e ≥ 0 for all e ∈ E and for each node v ∈ V there is some matching in M* that misses v (that
is, no edge in the matching covers v). Let G′ be the graph formed by those edges e ∈ E having
w_e > 0 and let S denote its node set. … We will show that each matching in M* satisfies
x(γ(S)) = (|S| − 1)/2,   (6.9)".

Hypotheses: `G` loopless; `w^T x ≤ t` is valid for `M(G)` and `{x ∈ M(G) : w^T x = t}` is a facet
of `M(G)`; `w ≥ 0`; every node is missed by some matching `M` with `w^T χ_M = t`; `S` is the set
of ends of edges with `w_e > 0`. Conclusion: every matching `M` with `w^T χ_M = t` has
`|M ∩ γ(S)| = χ_M(γ(S)) = (|S| − 1)/2`.

**Formalization Note.** `G` is loopless, as in the corrected Theorem 6.20. Validity of (6.8) is
the reading of "(6.8) induces a facet": the proof uses it (removing an edge `e` with `w_e < 0`
"would violate (6.8)"). -/
theorem eq_6_9 {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E) (hG : G.IsLoopless)
    (w : E → ℝ) (t : ℝ) (hvalid : IsValid G.matchingPolytope w t)
    (hfacet : IsFacet G.matchingPolytope (inducedFace G.matchingPolytope w t))
    (hw : ∀ e : E, 0 ≤ w e)
    (hmiss : ∀ v : V, ∃ M : Finset E, G.IsMatching M ∧ w ⬝ᵥ charVec M = t ∧
      ∀ e ∈ M, v ∉ G.ends e)
    (S : Finset V) (hS : ∀ v : V, v ∈ S ↔ ∃ e : E, 0 < w e ∧ v ∈ G.ends e)
    (M : Finset E) (hM : G.IsMatching M) (hMt : w ⬝ᵥ charVec M = t) :
    ∑ e ∈ G.gamma S, charVec M e = ((S.card : ℝ) - 1) / 2 := by sorry

end CombOpt.MatchingPolytope
