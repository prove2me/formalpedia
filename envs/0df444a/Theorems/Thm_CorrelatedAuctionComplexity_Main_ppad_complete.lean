-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_ppad_complete
-- name    : CorrelatedAuctionComplexity.Main.ppad_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:02.491969+00:00
-- url     : https://prove2.me/theorems/d159ee58-5d29-4a5e-8e4f-1dbb15ee575c
-- title:
--   Theorem 1 — Computing approximate mixed Bayes–Nash equilibria is PPAD-complete
-- statement:
--   There is a positive constant $\varepsilon$, independent of every auction parameter, such that computing an $\varepsilon$-approximate mixed Bayes–Nash equilibrium in an explicitly given normalized DFPA with a common correlated prior is PPAD-complete. Hardness holds at exactly the specified three bids:
--
--   $$\exists\varepsilon>0:\quad\mathrm{DFPA}_{\varepsilon}\text{ is PPAD-complete},\qquad\mathrm{DFPA}_{\varepsilon,\ B=\{0,1/5,2/5\}}\text{ is PPAD-hard}.$$
--
--   The general problem includes all finite rational bid sets and all finite rational correlated priors. Membership and hardness use standard machine-time search reductions and a concrete End-of-Line problem. Profiles must obey no overbidding, while each conditional equilibrium inequality tests all pure bids.
--
--   Differences from the source:
--   - encoding: explicit binary rational inputs and explicitly listed approximate equilibrium probabilities → canonical self-delimiting binary records and rational answer strings with the polynomial witnessBound; reason: standard finite search representation; grid rounding supplies a polynomial-size approximate answer without assuming rational exact equilibria
--   - encoding: there exists a fixed real approximation constant greater than zero → there exists a fixed positive rational approximation constant before any instance; reason: a smaller positive rational tolerance is admissible by density and monotonicity of approximation; all input instances and the restricted hardness clause are retained
--   - encoding: D given as a list of points in [0,1]^n with their probabilities → the listed points must be pairwise distinct with positive rational masses summing to 1 (DFPA.WellFormed 1); reason: a list with repeated points or zero-mass points is converted in polynomial time to this canonical list of the same distribution, with identical types, conditional priors and equilibria
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Theorem 1, p. 3 (PDF p. 3)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem ppad_complete :
    ∃ ε : ℚ, 0 < ε ∧ PPADComplete (dAuctionSearch ε) ∧ PPADHard (dAuctionSearch ε true) := by sorry

end CorrelatedAuctionComplexity.Main
