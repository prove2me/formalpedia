-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_expected_requests
-- name    : FairShareAlmostAll.Slack.expected_requests
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:23.772953+00:00
-- url     : https://prove2.me/theorems/5ff918b8-dfc0-4313-9aed-796e3ebce454
-- title:
--   Claim 2.5 — Expected requests from marginal bounds
-- statement:
--   Fix an active agent $i$, any $a_i\ge0$, and any bundle law $Q_i$ with each item marginal at most $a_i$. Then
--   $$\mathbb E_{P\sim Q_i}[\lambda_{iP}]\le a_i,\qquad\mathbb E_{P\sim Q_i}[d_{j,iP}]\le a_i|C_j|\quad(2\le j\le H).$$
--   No configuration-support or certificate assumption is imposed on this law. The tail fraction is explicitly zero when total tail value is zero.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 9 (PDF p. 10), Claim 2.5; Appendix A, printed p. 28 (PDF p. 29); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

namespace FairShareAlmostAll.Slack

theorem expected_requests {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q)
    (i : Fin n) (hi : i ∈ active X) (a : ℝ) (ha : 0 ≤ a)
    (Q : FiniteLaw (Finset (Fin m)))
    (hQ : ∀ g, probability Q (fun P => g ∈ P) ≤ a) :
    expectation Q (tailFraction X q i) ≤ a ∧
    ∀ j ∈ Finset.Icc 2 (bucketCount q m),
      expectation Q (request X q j i) ≤ a * (bucket q m j).card := by sorry

end FairShareAlmostAll.Slack
