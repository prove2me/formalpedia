-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_tie_dp_polytime
-- name    : CorrelatedAuctionComplexity.Main.tie_dp_polytime
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T07:05:32.990184+00:00
-- url     : https://prove2.me/theorems/9c18f6df-90ab-42ed-8e16-9a4593a39d67
-- title:
--   Lemma 15 — Polynomial-time tie-count utility evaluator
-- statement:
--   There is one Cook-machine-computable binary function, polynomial time in the request length, which decodes an HDFPA $H$, a rational mixed profile $\sigma$, and a bidder $i$ and outputs the canonical binary rational code of
--
--   $$
--   \sum_{e:\,i\in S_e} w_e\sum_{b\in B}\sigma_i(b)\,
--   \operatorname{edgeUtilityDP}(H,\sigma,e,i,b).
--   $$
--
--   The evaluator uses exact binary rational arithmetic and the quadratic-size recurrence `tieStep`/`tieTable`, summing the tie-sharing terms $D_{m,k}/(k+1)$ exactly. It is total on arbitrary bit strings; the displayed output equation is required on every well-formed utility request produced by `utilityRequest`.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 15 and its proof, pp. 19–20 (PDF pp. 19–20); explicit Cook-machine and binary-rational encoding convention.

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

open scoped BigOperators

theorem tie_dp_polytime :
    ∃ f : Bits → Bits, CookPvsNP.PolyTimeComputable f ∧
      ∀ (n : ℕ) (H : HDFPA (Fin n)) (p : H.RatProfile) (i : Fin n),
        f (utilityRequest H p i) = encodeRat
          (∑ e : Fin H.edges.length, (H.edge e).weight *
            (if i ∈ (H.edge e).participants then
              ∑ b : H.Bid, p i b * edgeUtilityDP H p e i b else 0)) := by sorry
