-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_utilityQ_eq_tie_dp
-- name    : CorrelatedAuctionComplexity.Main.utilityQ_eq_tie_dp
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T07:04:37.621915+00:00
-- url     : https://prove2.me/theorems/5538febc-a604-4d4f-abc9-2a252e906211
-- title:
--   Lemma 15 — Exact tie-count dynamic program for rational utility
-- statement:
--   For every rational mixed profile $\sigma$ of an HDFPA $H$ and every bidder $i$, the exact rational expected utility has the tie-count dynamic-programming form
--
--   $$
--   U_i(\sigma)=
--   \sum_{e:\,i\in S_e} w_e\sum_{b\in B}\sigma_i(b)\,
--   (v_i-b)\sum_{k=0}^{m_e}\frac{D^{e,b}_{m_e,k}}{k+1}.
--   $$
--
--   Here $m_e=|S_e\setminus\{i\}|$, and $D^{e,b}_{r,k}$ is computed by `tieTable` from the lower-than-$b$ and equal-to-$b$ probabilities of the other participants. Nonincident edges contribute zero. This is the exact rational identity underlying Lemma 15; it does not assume equilibrium or any bound on hyperedge size.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 15 and its proof, pp. 19–20 (PDF pp. 19–20).

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

open scoped BigOperators

theorem utilityQ_eq_tie_dp {n : ℕ} (H : HDFPA (Fin n)) (p : H.RatProfile) (i : Fin n) :
    H.utilityQ p i =
      ∑ e : Fin H.edges.length, (H.edge e).weight *
        (if i ∈ (H.edge e).participants then
          ∑ b : H.Bid, p i b * edgeUtilityDP H p e i b else 0) := by sorry
