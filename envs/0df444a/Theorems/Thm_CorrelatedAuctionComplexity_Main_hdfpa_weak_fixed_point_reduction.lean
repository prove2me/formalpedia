-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_weak_fixed_point_reduction
-- name    : CorrelatedAuctionComplexity.Main.hdfpa_weak_fixed_point_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T07:12:58.405519+00:00
-- url     : https://prove2.me/theorems/8aab17af-dad7-41db-a490-21b86d2ca387
-- title:
--   Lemma 16 — weak Nash fixed points decode to approximate equilibria
-- statement:
--   The variable-accuracy HDFPA equilibrium problem reduces in polynomial time to the rational weak approximate fixed-point problem for Nash's map. The instance map preserves the input $(H,\eta)$, and the answer map returns the same explicitly coded rational profile.
--
--   For $k=|B|$, a legal profile $\sigma$ with
--   $$
--   |F_H(\sigma)_{i,b}-\sigma_{i,b}|\le \frac{\eta^2}{16k^3}
--   $$
--   must be an $\eta$-Nash equilibrium after payoffs are normalized by $W_i$. Undoing this normalization gives
--   $$
--   U_i(b,\sigma_{-i})-U_i(\sigma)\le \eta W_i
--   $$
--   for every legal pure deviation $b\le v_i$. The polynomial answer-size bound and canonical profile code are unchanged.
--
--   **Formalization Note** The theorem includes polynomial-time computability of the instance and answer maps and correctness for every fixed-point-search answer, not merely the mathematical implication for one profile. For $\eta>1$, the normalized-payoff bound makes the equilibrium conclusion immediate; the cited weak-fixed-point argument handles the remaining range.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), proof of Lemma 16, pp. 20–21: normalization by Wi and application of [EY10, Proposition 2.3] with M=1 and tolerance η²/(16|B|³).

import Definitions.Def_CorrelatedAuctionComplexity_Main_NashFixedSearch

set_option autoImplicit false

theorem CorrelatedAuctionComplexity.Main.hdfpa_weak_fixed_point_reduction :
    CardinalMatching.SearchReduces hVariableAccuracy hNashFixedSearch := by sorry
