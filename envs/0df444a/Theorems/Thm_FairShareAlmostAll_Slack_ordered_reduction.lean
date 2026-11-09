-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_ordered_reduction
-- name    : FairShareAlmostAll.Slack.ordered_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:52.242196+00:00
-- url     : https://prove2.me/theorems/8eb5cf84-9bb3-4418-b303-2fe824c536d8
-- title:
--   Ordered-instance APS preservation and allocation transfer
-- statement:
--   Sort each agent's singleton values independently in descending order to obtain $v_i^{\rm ord}$. These values remain nonnegative and preserve total value and APS at the original entitlement. Every partial allocation $B$ of ranks admits an original partial allocation $A$ with
--   $$v_i(A_i)\ge v_i^{\rm ord}(B_i)\qquad\text{for every agent }i.$$
--   This is the unnumbered transfer obligation in Section 1.5. It permits the auxiliary common ordering without imposing an ordering hypothesis on Theorem 1.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - generalization: standing model W ≤ 1 → no bound on total entitlement; reason: sorting, APS preservation and the allocation transfer do not use the sum of budgets; restricting to W ≤ 1 recovers every source instance
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 7 (PDF p. 8), §1.5, Ordered goods and its unnumbered displayed transfer inequality; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack

theorem ordered_reduction {n m : ℕ} (X : Instance n m) (hn : 2 ≤ n) :
    (∀ i g, 0 ≤ orderedValue X i g) ∧
    (∀ i, Antitone (orderedValue X i)) ∧
    (∀ i, AnyPriceShare.Bidding.addVal (orderedValue X i) Finset.univ =
      AnyPriceShare.Bidding.addVal (X.value i) Finset.univ) ∧
    (∀ i, AnyPriceShare.Bidding.anyPrice (X.entitlement i)
      (AnyPriceShare.Bidding.addVal (orderedValue X i)) Finset.univ = target X i) ∧
    ∀ B : Fin n → Finset (Fin m), PartialAllocation B →
      ∃ A : Fin n → Finset (Fin m), PartialAllocation A ∧
        ∀ i, AnyPriceShare.Bidding.addVal (orderedValue X i) (B i) ≤
          AnyPriceShare.Bidding.addVal (X.value i) (A i) := by sorry

end FairShareAlmostAll.Slack
