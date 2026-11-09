-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_ppad_complete
-- name    : CorrelatedAuctionComplexity.Main.hdfpa_ppad_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:33.399338+00:00
-- url     : https://prove2.me/theorems/33dae0cc-b989-42d0-b4cd-09221964748c
-- title:
--   Theorem 2 — HDFPA completeness and restricted hardness
-- statement:
--   There is a positive constant $\varepsilon$, independent of the auction input, such that finding an $\varepsilon$-NE of a normalized HDFPA is PPAD-complete. The same constant has PPAD hardness under the stated restrictions:
--
--   $$\exists\varepsilon>0:\quad\mathrm{HDFPA}_{\varepsilon}\text{ is PPAD-complete},\qquad\mathrm{HDFPA}_{\varepsilon,\ B=\{0,1/4\},\ |S_e|\le4}\text{ is PPAD-hard}.$$
--
--   Completeness includes both membership and hardness in the standard End-of-Line based class. This intermediate target retains both sentences of the source theorem.
--
--   Differences from the source:
--   - encoding: explicit binary rational inputs and explicitly listed approximate equilibrium probabilities → canonical self-delimiting binary records and rational answer strings with the polynomial witnessBound; reason: standard finite search representation; grid rounding supplies a polynomial-size approximate answer without assuming rational exact equilibria
--   - encoding: there exists a fixed real approximation constant greater than zero → there exists a fixed positive rational approximation constant before any instance; reason: a smaller positive rational tolerance is admissible by density and monotonicity of approximation; all input instances and the restricted hardness clause are retained
--   - reading: introduction: the weighted hypergraph defines a distribution over subsets; Section 3.2: weights w_e need not sum to 1 → arbitrary positive rational edge weights (Section 3.2 model, the one Theorem 2 is proved in); reason: by footnote 3 a common rescaling of weights leaves the set of η-NE unchanged, so normalizing weights is a polynomial-time answer-preserving equivalence between the two readings
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Theorem 2, p. 4 (PDF p. 4)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem hdfpa_ppad_complete :
    ∃ ε : ℚ, 0 < ε ∧ PPADComplete (hAuctionSearch ε) ∧ PPADHard (hAuctionSearch ε true) := by sorry

end CorrelatedAuctionComplexity.Main
