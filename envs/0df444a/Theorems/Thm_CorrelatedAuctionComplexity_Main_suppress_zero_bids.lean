-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_suppress_zero_bids
-- name    : CorrelatedAuctionComplexity.Main.suppress_zero_bids
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:19.947833+00:00
-- url     : https://prove2.me/theorems/0337a724-3102-4f21-9df5-7cef1aa47dd7
-- title:
--   Lemma 17 — Suppressing zero bids in the shifted construction
-- statement:
--   Let $H$ be an unnormalized HDFPA with binary bids, values in $\{1/2,2,3,4\}$, and at most four participants per edge. Construct $A_H$ with shifted values, fifty dummy bidders, and the additional anchor masses. For every $\varepsilon\ge0$ and every real $\varepsilon$-approximate MBNE $\beta$ of $A_H$,
--
--   $$\beta_{x_i}(v_i+1)(0)\le10\varepsilon\qquad\text{for every original bidder }i.$$
--
--   Original anchors are included. The statement uses the unnormalized DFPA with values at most five, as in Section 5.1.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 17, p. 22 (PDF p. 22)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem suppress_zero_bids {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : HardFamily H) (ε : ℝ) (hε : 0 ≤ ε)
    (β : (shiftedDFPA H).Profile) (hβ : (shiftedDFPA H).IsMBNE ε β) :
    ∀ i : N, shiftedProbability H β i 0 ≤ 10*ε := by sorry

end CorrelatedAuctionComplexity.Main
