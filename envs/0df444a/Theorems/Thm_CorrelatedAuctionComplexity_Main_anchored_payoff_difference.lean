-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_anchored_payoff_difference
-- name    : CorrelatedAuctionComplexity.Main.anchored_payoff_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:18.913972+00:00
-- url     : https://prove2.me/theorems/93e6d964-8e95-4058-98ef-532bc0eabf89
-- title:
--   Claim 10 — Two active bidders with zero anchors
-- statement:
--   Let $m\ge0$, let distinct bidders $x,y$ have values in $\{2,3,4\}$, and let $z_1,\ldots,z_m$ be distinct fresh anchors of value $1/2$. For an edge $e$ on exactly these bidders, every legal real mixed profile satisfies
--
--   $$\Delta_x^e(p)=w_e\left[\left(\frac{v_x}{m+2}-\frac{v_x-1}{2}\right)p(y)+v_x-1-\frac{v_x}{m+2}\right].$$
--
--   The case $m=0$ is included. This formula retains the uniform tie among all zero bids.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Claim 10, p. 14 (PDF p. 14)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem anchored_payoff_difference {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (m : ℕ) (x y : N) (hxy : x ≠ y) (z : Fin m → N)
    (hz : (List.ofFn z).Nodup) (hfresh : ∀ j, z j ≠ x ∧ z j ≠ y)
    (hx : H.value x ∈ ({2,3,4} : Finset ℚ))
    (hy : H.value y ∈ ({2,3,4} : Finset ℚ)) (hvz : ∀ j, H.value (z j) = 1/2)
    (e : Fin H.edges.length)
    (he : (H.edge e).participants = {x,y} ∪ Finset.univ.image z)
    (p : N → ℝ) (hp : H.LegalBinary p) :
    H.delta p {e} x = ((H.edge e).weight : ℝ) *
      ((((H.value x : ℝ)/(m+2 : ℕ)) - ((H.value x : ℝ)-1)/2)*p y +
        (H.value x : ℝ)-1-(H.value x : ℝ)/(m+2 : ℕ)) := by sorry

end CorrelatedAuctionComplexity.Main
