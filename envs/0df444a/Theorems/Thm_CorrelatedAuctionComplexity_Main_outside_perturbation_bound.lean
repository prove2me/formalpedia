-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_outside_perturbation_bound
-- name    : CorrelatedAuctionComplexity.Main.outside_perturbation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:09.113183+00:00
-- url     : https://prove2.me/theorems/21cea509-1d4f-4e79-b90d-5d3584539877
-- title:
--   Claim 11 — Outside-gadget perturbation bound
-- statement:
--   Let $x$ have value 2 in a binary-bid HDFPA, and let $R$ be any finite selection of edge occurrences all containing $x$. Every legal real mixed profile satisfies
--
--   $$|\Delta_x^R(p)|\le\sum_{e\in R}w_e.$$
--
--   Repeated auctions retain their multiplicities. The estimate controls the total incentive supplied by edges outside a selected gadget.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Claim 11, p. 15 (PDF p. 15)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem outside_perturbation_bound {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x : N) (hx : H.value x = 2) (p : N → ℝ) (hp : H.LegalBinary p)
    (R : Finset (Fin H.edges.length)) (hR : ∀ e ∈ R, x ∈ (H.edge e).participants) :
    |H.delta p R x| ≤ ∑ e ∈ R, ((H.edge e).weight : ℝ) := by sorry

end CorrelatedAuctionComplexity.Main
