-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_utilityQ_eq_tie_dp_legal
-- name    : CorrelatedAuctionComplexity.Main.utilityQ_eq_tie_dp_legal
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T08:27:20.475845+00:00
-- url     : https://prove2.me/theorems/6f1116b8-0c54-4b80-94ad-4af8d77402ae
-- title:
--   Lemma 15 — Exact tie-count DP for a legal rational profile
-- statement:
--   For every legal rational mixed profile \(\sigma\) of an HDFPA \(H\), the exact rational expected utility of bidder \(i\) is
--   \[
--   U_i(\sigma)=\sum_{e:i\in S_e}w_e\sum_{b\in B}\sigma_i(b)\,
--   (v_i-b)\sum_{k=0}^{m_e}\frac{D^{e,b}_{m_e,k}}{k+1},
--   \]
--   where the tie table is computed from the lower-than-\(b\) and equal-to-\(b\) probabilities of the other participants. Legality gives normalized lotteries, including for nonparticipants; this hypothesis is essential because the unguarded statement is false when a nonparticipant has total mass different from one.
-- source:
--   Chen–Chen–Cui–Pires–Stockwell, STOC 2027 submission #324, Lemma 15 and proof, pp. 19–20. Legal profiles are the hypotheses of the statement; normalization repairs a missing hypothesis in the earlier auxiliary statement `utilityQ_eq_tie_dp`.

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

open scoped BigOperators

theorem CorrelatedAuctionComplexity.Main.utilityQ_eq_tie_dp_legal {n : ℕ}
    (H : HDFPA (Fin n)) (p : H.RatProfile) (hp : H.Legal (H.realProfile p)) (i : Fin n) :
    H.utilityQ p i =
      ∑ e : Fin H.edges.length, (H.edge e).weight *
        (if i ∈ (H.edge e).participants then
          ∑ b : H.Bid, p i b * edgeUtilityDP H p e i b else 0) := by sorry
