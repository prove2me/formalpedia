-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_conditional_edge_view
-- name    : CorrelatedAuctionComplexity.Main.conditional_edge_view
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:30.784001+00:00
-- url     : https://prove2.me/theorems/d35c37b8-c19f-431f-93e5-c251204e556b
-- title:
--   Observation 5 — Conditional-edge view
-- statement:
--   Let $H$ be a hypergraph auction and $\sigma$ a legal real mixed profile. For bidder $i$, draw an incident edge $e$ with probability $w_e/W_i$. For every $\eta\ge0$,
--
--   $$\sigma\text{ is an }\eta\text{-NE}\quad\Longleftrightarrow\quad\mathbb E[u_i^e(b)]\ge\mathbb E[u_i^e(b_i,b_{-i})]-\eta\quad\text{for every }i,b_i\in B_i.$$
--
--   The equivalence explains why approximation is normalized by each bidder's incident weight, rather than the total auction weight.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Observation 5, p. 11 (PDF p. 11)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem conditional_edge_view {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 1) (η : ℝ) (hη : 0 ≤ η)
    (σ : H.Profile) (hσ : H.Legal σ) :
    H.IsNE η σ ↔ ∀ i b, b.val ≤ H.value i →
      H.conditionalUtility (deviation σ i b) i - η ≤ H.conditionalUtility σ i := by sorry

end CorrelatedAuctionComplexity.Main
