-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_fixed_accuracy_membership
-- name    : CorrelatedAuctionComplexity.Main.hdfpa_fixed_accuracy_membership
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T08:42:52.084083+00:00
-- url     : https://prove2.me/theorems/445ac449-ea2c-408a-be2d-3edfd063e05a
-- title:
--   Lemma 16 — HDFPA membership at fixed positive accuracy
-- statement:
--   For every fixed positive rational accuracy $\varepsilon$, the problem of finding an $\varepsilon$-approximate Nash equilibrium of an explicitly encoded normalized hypergraph discrete first-price auction belongs to PPAD:
--
--   $$0<\varepsilon\quad\Longrightarrow\quad \mathrm{HDFPA}_{\varepsilon}\in\mathrm{PPAD}.$$
--
--   The search relation requires a legal rational mixed profile, obeys no overbidding, and measures bidder $i$'s equilibrium error additively by $\varepsilon W_i$, where $W_i$ is the total incident edge weight. This is the constant-accuracy specialization of Lemma 16, with the accuracy prefix fixed rather than supplied as part of each input.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 16 and Section 4.7, pp. 20–21; fixed-accuracy interface of Theorem 2, p. 4.

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

theorem CorrelatedAuctionComplexity.Main.hdfpa_fixed_accuracy_membership (ε : ℚ) (hε : 0 < ε) :
    InPPAD (hAuctionSearch ε) := by sorry
