-- Prove2me | Theorems.Thm_CombOpt_MatroidPolytope_maxWeightBasis_iff
-- name    : CombOpt.MatroidPolytope.maxWeightBasis_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:25.38031+00:00
-- url     : https://prove2.me/theorems/03d95f0b-6b5e-442f-b99a-6e72ccf87fce
-- title:
--   Corollary 8.7 — exchange characterization of a maximum-weight basis
-- statement:
--   Let $M=(S,\mathcal I)$ be a matroid, let $c\in\mathbb R^S$, and let $J$ be a basis of $M$ (a maximal independent subset of $S$). Then $c(J)\ge c(J')$ for every basis $J'$ of $M$ if and only if
--   $$e\notin J,\ f\in J,\ (J\cup\{e\})\setminus\{f\}\in\mathcal I \ \Longrightarrow\ c_e\le c_f.$$
--
--   Weights may be negative. The corollary is used for spanning trees of graphs, where the bases of the forest matroid are the spanning trees of a connected graph.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Corollary 8.7, p. 280 (PDF p. 287)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_weight

namespace CombOpt.MatroidPolytope

/-- **Corollary 8.7: optimality conditions for a maximum-weight basis.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Corollary 8.7, p. 280 (PDF p. 287): "Let M = (S, I) be a matroid, let c ∈ R^S, and let J
be a basis of M. Then J is a maximum weight basis with respect to c if and only if e ∉ J, f ∈ J,
(J ∪ {e})\{f} ∈ I imply c_e ≤ c_f."

A *basis of M* is a basis of the whole ground set `S` (p. 275), i.e. `IsBasisOf I Finset.univ`;
`J` is a maximum-weight basis when `c(J') ≤ c(J)` for every basis `J'` of `M`. -/
theorem maxWeightBasis_iff {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α → Prop)
    (hI : IsMatroid I) (c : α → ℝ) (J : Finset α) (hJ : IsBasisOf I Finset.univ J) :
    (∀ J' : Finset α, IsBasisOf I Finset.univ J' → weight c J' ≤ weight c J) ↔
      ∀ e f, e ∉ J → f ∈ J → I ((insert e J).erase f) → c e ≤ c f := by sorry

end CombOpt.MatroidPolytope
