-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_proportional_aps_high_probability
-- name    : FairShareAlmostAll.Slack.Supplement.proportional_aps_high_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:14:20.738669+00:00
-- url     : https://prove2.me/theorems/fba69710-c5d6-494f-918b-60981f85fa3e
-- title:
--   Theorem 2 — Ex-ante proportionality and APS with probability $1-\varepsilon$
-- statement:
--   Let $0<\varepsilon\le1/2$ be real. Consider an instance with $n\ge2$ agents, nonnegative additive valuations $v_i$ and entitlements $b_i>0$ with $W=\sum_i b_i=1$ and
--
--   $$\max_i b_i\le\frac{\varepsilon^3}{262144\log(16/\varepsilon)}.$$
--
--   Then there is a randomized allocation $A$ such that, for every agent $i$,
--
--   $$\mathbb E[v_i(A_i)]\ge b_i\,v_i(M),\qquad \Pr\bigl[v_i(A_i)\ge\mathrm{APS}_i(b_i)\bigr]\ge1-\varepsilon.$$
--
--   The probability guarantee is individual: each agent separately succeeds with probability at least $1-\varepsilon$ under the same randomized allocation; it does not assert that all agents succeed simultaneously. This is the paper's first best-of-both-worlds result; with equal entitlements it yields ex-ante proportionality together with the maximin share with probability $1-O((\log n/n)^{1/3})$.
--
--   **Formalization Note** A randomized allocation is a `FiniteLaw` over complete maps $\sigma$ from goods to agents; a partial allocation can be completed without decreasing any value. The statement holds for every real $\varepsilon$ in the range; the paper's proof assumes "for simplicity" that $1/\varepsilon$ is an integer, and that convenience is not a hypothesis here.
--
--   Differences from the source:
--   - encoding: randomized (partial or complete) allocation → `FiniteLaw` over complete allocations; reason: by nonnegativity, assigning leftover goods preserves both guarantees, so the two existence statements are equivalent
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 4 (PDF p. 5), Theorem 2; proof §4.3, printed pp. 18–19 (PDF pp. 19–20); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem proportional_aps_high_probability {n m : ℕ} (X : Instance n m) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hW : totalEntitlement X = 1)
    (hb : ∀ i, X.entitlement i ≤ ε ^ 3 / (262144 * Real.log (16 / ε))) :
    ∃ D : FiniteLaw (Fin m → Fin n), ∀ i,
      X.entitlement i * addVal (X.value i) Finset.univ ≤
        expectation D (fun σ => addVal (X.value i) (allocBundle σ i)) ∧
      1 - ε ≤ probability D (fun σ =>
        target X i ≤ addVal (X.value i) (allocBundle σ i)) := by sorry

end FairShareAlmostAll.Slack.Supplement
