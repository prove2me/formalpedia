-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_dfpa_membership
-- name    : CorrelatedAuctionComplexity.Main.dfpa_membership
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:14.93781+00:00
-- url     : https://prove2.me/theorems/da45a605-32f1-4a9a-982c-6ef6324519ff
-- title:
--   Lemma 20 — DFPA membership with binary accuracy input
-- statement:
--   For every normalized explicitly listed rational DFPA, finding an approximate mixed Bayes–Nash equilibrium is in PPAD when its positive rational accuracy is supplied in binary:
--
--   $$(A,\varepsilon)\longmapsto\text{a legal rational }\varepsilon\text{-MBNE},\qquad\varepsilon>0,\quad\text{is in PPAD}.$$
--
--   The prior may be arbitrarily correlated. Every bidder and every supported type satisfies its conditional deviation inequalities. This covers the entire input class, beyond the hardness construction.
--
--   Differences from the source:
--   - encoding: explicit binary rational inputs and explicitly listed approximate equilibrium probabilities → canonical self-delimiting binary records and rational answer strings with the polynomial witnessBound; reason: standard finite search representation; grid rounding supplies a polynomial-size approximate answer without assuming rational exact equilibria
--   - encoding: D given as a list of points in [0,1]^n with their probabilities → the listed points must be pairwise distinct with positive rational masses summing to 1 (DFPA.WellFormed 1); reason: a list with repeated points or zero-mass points is converted in polynomial time to this canonical list of the same distribution, with identical types, conditional priors and equilibria
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 20, p. 24 (PDF p. 24)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem dfpa_membership : InPPAD dVariableAccuracy := by sorry

end CorrelatedAuctionComplexity.Main
