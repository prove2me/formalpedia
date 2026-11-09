-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_singleton_payoff_difference
-- name    : CorrelatedAuctionComplexity.Main.singleton_payoff_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:05.602102+00:00
-- url     : https://prove2.me/theorems/44991073-80ba-44d9-85ec-56fcf54822f3
-- title:
--   Claim 9 — Singleton payoff difference
-- statement:
--   In a binary-bid HDFPA let bidder $x$ have value in $\{2,3,4\}$, and let $e$ be a weighted edge whose only participant is $x$. Every legal real mixed profile satisfies
--
--   $$\Delta_x^e(p)=-w_e.$$
--
--   A singleton auction therefore contributes a fixed negative payoff difference, independent of the other bidders' strategies.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Claim 9, p. 14 (PDF p. 14)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem singleton_payoff_difference {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x : N) (hx : H.value x ∈ ({2,3,4} : Finset ℚ))
    (e : Fin H.edges.length) (he : (H.edge e).participants = {x})
    (p : N → ℝ) (hp : H.LegalBinary p) :
    H.delta p {e} x = -((H.edge e).weight : ℝ) := by sorry

end CorrelatedAuctionComplexity.Main
