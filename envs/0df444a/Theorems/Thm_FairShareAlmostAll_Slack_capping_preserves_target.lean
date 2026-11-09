-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_capping_preserves_target
-- name    : FairShareAlmostAll.Slack.capping_preserves_target
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:54.064604+00:00
-- url     : https://prove2.me/theorems/db642358-ca8e-47a8-82dc-cc1338148929
-- title:
--   Claim 2.1 — Capping preserves the target
-- statement:
--   Under the standing assumptions of Section 2, fix an active agent $i$ and any APS certificate $D_i$ for $t_i$. Capping normalized singleton values at one preserves the target throughout its support, and implies
--   $$D_i(P)>0\Rightarrow u_i(P)\ge1,\qquad u_i(M)\ge1/b_i.$$
--   The total-value bound supplies the size lower bound needed for the bucket construction.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 8 (PDF p. 9), Claim 2.1; Appendix A, printed p. 27 (PDF p. 28); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

namespace FairShareAlmostAll.Slack

theorem capping_preserves_target {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q)
    (i : Fin n) (hi : i ∈ active X) (D : FiniteLaw (Finset (Fin m)))
    (hD : certificate (X.value i) (X.entitlement i) (target X i) D) :
    (∀ P, 0 < D.weight P → 1 ≤ cappedValue X i P) ∧
      1 / X.entitlement i ≤ cappedValue X i Finset.univ := by sorry

end FairShareAlmostAll.Slack
