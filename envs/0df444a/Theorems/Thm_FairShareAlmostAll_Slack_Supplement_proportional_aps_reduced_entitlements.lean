-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_proportional_aps_reduced_entitlements
-- name    : FairShareAlmostAll.Slack.Supplement.proportional_aps_reduced_entitlements
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:14:47.318583+00:00
-- url     : https://prove2.me/theorems/549f80ac-62ee-47d4-ad10-2fc3439ce52c
-- title:
--   Theorem 3 — Ex-ante proportionality and APS at reduced entitlements in every outcome
-- statement:
--   Let $0<\varepsilon\le1/2$ be real. Consider an instance with $n\ge2$ agents, nonnegative additive valuations $v_i$ and entitlements $b_i>0$ with $W=\sum_i b_i=1$ and
--
--   $$\max_i b_i\le\frac{\varepsilon^3}{262144\log(16/\varepsilon)}.$$
--
--   Then there is a randomized allocation $A$ such that, for every agent $i$,
--
--   $$\mathbb E[v_i(A_i)]\ge b_i\,v_i(M),\qquad v_i(A_i)\ge\mathrm{APS}_i\bigl((1-\varepsilon)b_i\bigr)\ \text{in every outcome}.$$
--
--   The ex-ante bound is at the original entitlement $b_i$; the ex-post share is the AnyPrice share at the reduced budget $(1-\varepsilon)b_i$. With equal entitlements it gives ex-ante proportionality together with an ex-post 1-out-of-$(n+O(n^{2/3}\log^{1/3}n))$ maximin share.
--
--   **Formalization Note** A randomized allocation is a `FiniteLaw` over complete maps $\sigma$; "every outcome" is every $\sigma$ of positive weight. The reduced share is the published `anyPrice` at budget $(1-\varepsilon)b_i$ over all goods. The statement holds for every real $\varepsilon$ in the range, without the proof's "$1/\varepsilon$ an integer" convenience.
--
--   Differences from the source:
--   - encoding: randomized (partial or complete) allocation → `FiniteLaw` over complete allocations; reason: by nonnegativity, assigning leftover goods preserves both guarantees, so the two existence statements are equivalent
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 4 (PDF p. 5), Theorem 3; proof §4.3, printed p. 19 (PDF p. 20); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem proportional_aps_reduced_entitlements {n m : ℕ} (X : Instance n m) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hW : totalEntitlement X = 1)
    (hb : ∀ i, X.entitlement i ≤ ε ^ 3 / (262144 * Real.log (16 / ε))) :
    ∃ D : FiniteLaw (Fin m → Fin n), ∀ i,
      X.entitlement i * addVal (X.value i) Finset.univ ≤
        expectation D (fun σ => addVal (X.value i) (allocBundle σ i)) ∧
      ∀ σ, 0 < D.weight σ →
        anyPrice ((1 - ε) * X.entitlement i) (addVal (X.value i)) Finset.univ ≤
          addVal (X.value i) (allocBundle σ i) := by sorry

end FairShareAlmostAll.Slack.Supplement
