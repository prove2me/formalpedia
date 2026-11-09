-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_configuration_feasibility
-- name    : FairShareAlmostAll.Slack.configuration_feasibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:21.033107+00:00
-- url     : https://prove2.me/theorems/74e9c45f-8fa9-41b8-ab51-98373d9aff80
-- title:
--   Claim 3.1 — Feasibility
-- statement:
--   Let $D_i$ be APS certificates for active agents, and condition them on avoiding the first bucket. Every conditioning event has positive probability. The resulting nonnegative weights sum to one, have nonempty positive support consisting of configurations, and satisfy
--   $$\sum_{P\in\mathcal P_i}\widetilde D_i(P)=1,\qquad\sum_{i\in N_+}\sum_{P\in\mathcal P_i}d_{j,iP}\widetilde D_i(P)\le|S_{j-1}|.$$
--   This certifies feasibility of exactly the Section 3 configuration polytope. The sufficient slack is extended to support every real epsilon in the goal.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - generalization: W ≤ 1 − 8/q in Section 3 → W ≤ 1 − 15/(2q); reason: the same feasibility estimate W/(1−qc) ≤ 1−5/q holds; the remaining Section 3 arguments use feasibility and the unchanged cap, and every source instance satisfies this relaxed bound
--   - encoding: coordinates indexed by active agents and positive conditional support → total finite arrays with every unused coordinate constrained to zero; reason: zero extension is an affine bijection and preserves feasibility and midpoint vertexhood
--   - encoding: the conditioning and support are well-defined in the paragraph preceding Claim 3.1 → conditioning positivity, normalized nonnegative weights, nonempty support and configuration membership are explicit conclusions; reason: these are exactly the source construction’s preceding assertions, made operational without adding hypotheses
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 10 (PDF p. 11), Claim 3.1 and its proof; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets
import Definitions.Def_FairShareAlmostAll_Slack_ConfigurationPolytope

namespace FairShareAlmostAll.Slack

theorem configuration_feasibility {n m : ℕ} (X : Instance n m) (q : ℕ) (h : SlackAssumptions X q)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (hD : ∀ i ∈ active X, certificate (X.value i) (X.entitlement i) (target X i) (D i)) :
    (∀ i ∈ active X, 0 < avoidanceMass q (D i) ∧
      (∑ P, conditionedWeight q (D i) P) = 1 ∧
      (∀ P, 0 ≤ conditionedWeight q (D i) P) ∧
      (configurationSupport q (D i)).Nonempty ∧
      (∀ P ∈ configurationSupport q (D i), Configuration X q i P)) ∧
    Feasible X q D (conditionedPoint X q D) := by sorry

end FairShareAlmostAll.Slack
