-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_cutoff_bound
-- name    : FairShareAlmostAll.Slack.Supplement.cutoff_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:55.184116+00:00
-- url     : https://prove2.me/theorems/9c2fde54-fce9-45ba-8900-6e1ae98f0245
-- title:
--   Claim 2.4 — Cutoff bound $h_i\le 2+2q\log(1/b_i)$
-- statement:
--   Work under the standing assumptions of Section 2: $n\ge2$ agents, an integer $q\ge16$, total entitlement $W\le1$, entitlements $b_i\le1/q^2$, a nonempty set $N_+$ of active agents (those with positive APS target $t_i$), and goods ordered so that every valuation is nonincreasing. The buckets $C_1,\dots,C_H$ have prescribed sizes $w_h=\lceil q(1+1/q)^{h-1}\rceil$, and the cutoff $h_i$ of an active agent is the first full bucket $h<H$ with $|C_h|\ge q/b_i$, or $H$ if there is none. Then every active agent $i$ satisfies
--
--   $$h_i\le 2+2q\log(1/b_i),$$
--
--   with the natural logarithm.
--
--   The claim bounds how many buckets lie in an agent's head; it is used in the Markov-inequality step of Proposition 4.1, which conditions each certificate on configurations with small contribution to the jointly controlled sums.
--
--   Differences from the source:
--   - encoding: ranks $1,\dots,m$ and buckets as rank intervals → goods `Fin m` and the live mission's published bucket, cutoff and active-set definitions; reason: the same objects under zero-based indexing, reused unchanged from the live mission
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 9 (PDF p. 10), Claim 2.4; proof Appendix A, printed pp. 27–28 (PDF pp. 28–29); standing assumptions §2, printed p. 7 (PDF p. 8); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem cutoff_bound {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q)
    (i : Fin n) (hi : i ∈ active X) :
    (cutoff X q i : ℝ) ≤ 2 + 2 * (q : ℝ) * Real.log (1 / X.entitlement i) := by sorry

end FairShareAlmostAll.Slack.Supplement
