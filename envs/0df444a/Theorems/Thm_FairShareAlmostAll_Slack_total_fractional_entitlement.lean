-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_total_fractional_entitlement
-- name    : FairShareAlmostAll.Slack.total_fractional_entitlement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:55.99914+00:00
-- url     : https://prove2.me/theorems/68b3d79b-7831-4d51-8051-dd3fe24b8412
-- title:
--   Claim 3.3 — Total fractional entitlement
-- statement:
--   At every vertex of the configuration polytope, the total original entitlement of fractional agents obeys
--   $$\sum_{i\in F}b_i\le\frac1{2q}.$$
--   The cap is $c=1/(32q^2\log q)$ with integer $q\ge16$. The exact bound is the reserve capacity used in Claim 3.4; entitlements are never renormalized.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - generalization: W ≤ 1 − 8/q in Section 3 → W ≤ 1 − 15/(2q); reason: the same feasibility estimate W/(1−qc) ≤ 1−5/q holds; the remaining Section 3 arguments use feasibility and the unchanged cap, and every source instance satisfies this relaxed bound
--   - encoding: coordinates indexed by active agents and positive conditional support → total finite arrays with every unused coordinate constrained to zero; reason: zero extension is an affine bijection and preserves feasibility and midpoint vertexhood
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 12 (PDF p. 13), Claim 3.3; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets
import Definitions.Def_FairShareAlmostAll_Slack_ConfigurationPolytope

namespace FairShareAlmostAll.Slack

theorem total_fractional_entitlement {n m : ℕ} (X : Instance n m) (q : ℕ) (h : SlackAssumptions X q)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (hD : ∀ i ∈ active X, certificate (X.value i) (X.entitlement i) (target X i) (D i))
    (x : Fin n → Finset (Fin m) → ℝ) (hx : Vertex X q D x) :
    ∑ i ∈ fractionalAgents X q D x, X.entitlement i ≤ 1 / (2 * (q : ℝ)) := by sorry

end FairShareAlmostAll.Slack
