-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_aps_certificates
-- name    : FairShareAlmostAll.Slack.aps_certificates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:40.818711+00:00
-- url     : https://prove2.me/theorems/9bdda3d4-17b7-4d22-b96f-430c545f3cc6
-- title:
--   Lemma 1.1 — APS certificates
-- statement:
--   Let $i$ be an agent and $t\ge0$. The target is attainable by an APS certificate exactly when it is at most her APS:
--   $$t\le\operatorname{APS}_i(b_i)\ \Longleftrightarrow\ \exists D:\quad D(P)>0\Rightarrow v_i(P)\ge t,\quad\Pr_{P\sim D}(g\in P)\le b_i\ \ (g\in M).$$
--   The distribution ranges over all bundles. Both implications include $t=0$, $t=\operatorname{APS}_i(b_i)$ and the empty-good case. The published price/packing equality is reused; the attained endpoint remains part of this new certificate bridge.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 7 (PDF p. 8), Lemma 1.1; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack

theorem aps_certificates {n m : ℕ} (X : Instance n m) (hn : 2 ≤ n)
    (hW : totalEntitlement X ≤ 1) (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    t ≤ target X i ↔ ∃ D : FiniteLaw (Finset (Fin m)),
      certificate (X.value i) (X.entitlement i) t D := by sorry

end FairShareAlmostAll.Slack
