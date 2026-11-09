-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_binary_deviation_inequalities
-- name    : CorrelatedAuctionComplexity.Main.binary_deviation_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:41.757327+00:00
-- url     : https://prove2.me/theorems/7df2d4da-dc8e-42e0-963c-f44b65eeff4b
-- title:
--   Claim 8 — Binary-bid deviation inequalities
-- statement:
--   Let $p$ be any $\eta$-NE in the binary-bid auction model, with $\eta\ge0$. For every bidder $x$, write $p(x)$ for her probability of bidding one and $\Delta_x$ for the weighted advantage of one over zero. Then
--
--   $$\Delta_x(p)>0\Rightarrow(1-p(x))\Delta_x(p)\le\eta W_x,\qquad\Delta_x(p)<0\Rightarrow-p(x)\Delta_x(p)\le\eta W_x.$$
--
--   These inequalities include the forced-zero anchors and connect deviation incentives with mixed probabilities.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Claim 8, p. 13 (PDF p. 13)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem binary_deviation_inequalities {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (η : ℝ) (hη : 0 ≤ η) (p : N → ℝ)
    (hne : H.IsNE η (H.binaryProfile p)) :
    ∀ x, (0 < H.totalDelta p x → (1-p x)*H.totalDelta p x ≤ η*H.incidentWeight x) ∧
      (H.totalDelta p x < 0 → -(p x)*H.totalDelta p x ≤ η*H.incidentWeight x) := by sorry

end CorrelatedAuctionComplexity.Main
