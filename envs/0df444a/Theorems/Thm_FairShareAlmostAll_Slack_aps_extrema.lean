-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_aps_extrema
-- name    : FairShareAlmostAll.Slack.aps_extrema
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:44.490884+00:00
-- url     : https://prove2.me/theorems/e8ef7413-4dec-485c-8b2e-0d67a67e6ffc
-- title:
--   APS extrema are attained, including the empty-good convention
-- statement:
--   For any agent $i$, APS is zero when $m=0$. For $m>0$, every normalized price vector has a nonempty bounded set of affordable bundle values, and its supremum is attained. The set of these maxima is nonempty, bounded below, and has an attained infimum equal to $t_i$:
--   $$\operatorname{APS}_i(b_i)=\min_{\pi\ge0,\ \sum_g\pi_g=1}\max_{\pi(P)\le b_i}v_i(P).$$
--   This supporting obligation verifies that the reused real infimum and supremum implement the source's extrema.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - generalization: standing model n ≥ 2 → arbitrary n, with an agent i : Fin n; reason: APS extrema depend only on one valuation and its positive budget; the same extrema statement holds for a single agent and specializes to every source instance
--   - generalization: standing model W ≤ 1 → no bound on total entitlement; reason: the price and affordable-value sets depend only on this agent’s original budget, not on other entitlements; restricting to W ≤ 1 recovers the source
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 3 (PDF p. 4), §1.1, APS definition (unnumbered); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack

theorem aps_extrema {n m : ℕ} (X : Instance n m) (i : Fin n) :
    (m = 0 → target X i = 0) ∧
    (0 < m →
      (∀ p, ValidPrice p → (affordableValues (X.value i) (X.entitlement i) p).Nonempty ∧
        BddAbove (affordableValues (X.value i) (X.entitlement i) p) ∧
        sSup (affordableValues (X.value i) (X.entitlement i) p) ∈
          affordableValues (X.value i) (X.entitlement i) p) ∧
      (priceOutcomes (X.value i) (X.entitlement i)).Nonempty ∧
      BddBelow (priceOutcomes (X.value i) (X.entitlement i)) ∧
      target X i ∈ priceOutcomes (X.value i) (X.entitlement i) ∧
      target X i = sInf (priceOutcomes (X.value i) (X.entitlement i))) := by sorry

end FairShareAlmostAll.Slack
