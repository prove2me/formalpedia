-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_hardness
-- name    : CorrelatedAuctionComplexity.Main.hdfpa_hardness
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T08:43:15.474154+00:00
-- url     : https://prove2.me/theorems/f3700480-d1c9-41e2-b5c7-7a9fa32c8815
-- title:
--   Theorem 2 — HDFPA hardness, including the binary-bid four-player restriction
-- statement:
--   There is a fixed positive rational accuracy $\varepsilon$, independent of the auction instance, for which approximate equilibrium computation in a hypergraph discrete first-price auction is PPAD-hard. The same accuracy gives hardness on the restricted family:
--
--   $$\mathrm{HDFPA}_{\varepsilon}\ \text{is PPAD-hard},\qquad
--   \mathrm{HDFPA}_{\varepsilon,\;B=\{0,1/4\},\;|S_e|\le4}\ \text{is PPAD-hard}.$$
--
--   The restricted instances have exactly the two bids $0$ and $1/4$ and at most four participants per edge occurrence. The unrestricted conclusion follows because the restricted family is included in the general one. This is precisely the hardness half of Theorem 2; the proof uses Section 4.6's gadget reduction from bounded-input generalized circuits and normalization by $4$.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Theorem 2, p. 4; PPAD-hardness proof in Section 4.6, p. 19, using Theorem 7, p. 12.

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

theorem CorrelatedAuctionComplexity.Main.hdfpa_hardness :
    ∃ ε : ℚ, 0 < ε ∧ PPADHard (hAuctionSearch ε) ∧
      PPADHard (hAuctionSearch ε true) := by sorry
