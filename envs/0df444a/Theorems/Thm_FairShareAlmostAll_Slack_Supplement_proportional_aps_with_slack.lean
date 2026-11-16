-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_proportional_aps_with_slack
-- name    : FairShareAlmostAll.Slack.Supplement.proportional_aps_with_slack
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:11:55.506729+00:00
-- url     : https://prove2.me/theorems/8c6513b1-2864-4f19-946f-1a251cb76ee2
-- title:
--   Proposition 4.1 — Normalized proportionality and APS with entitlement slack
-- statement:
--   Fix $0<\delta\le1/2$ with $1/\delta$ an integer, and set
--
--   $$\kappa_\delta=\frac{\delta^3}{32768\log(8/\delta)}.$$
--
--   Consider an instance with $n\ge2$ agents, nonnegative additive valuations $v_i$ and entitlements satisfying
--
--   $$0<W=\sum_{i\in N}b_i\le1-\delta,\qquad 0<b_i\le\kappa_\delta\quad(i\in N).$$
--
--   There is a randomized complete allocation $A$ such that, for every agent $i$,
--
--   $$\mathbb E[v_i(A_i)]\ge\frac{b_i}{W}\,v_i(M),\qquad v_i(A_i)\ge\mathrm{APS}_i(b_i)\ \text{in every outcome}.$$
--
--   Here $\mathrm{APS}_i(b_i)$ is the AnyPrice share at the original entitlement. This normalized best-of-both-worlds result is the common source of Theorems 2 and 3.
--
--   **Formalization Note** A randomized complete allocation is a `FiniteLaw` over maps $\sigma$ from goods to agents; "every outcome" is every $\sigma$ of positive weight. The integrality of $1/\delta$ is part of the source statement and is kept.
--
--   Differences from the source:
--   - encoding: the hypothesis $0<W$ → omitted; reason: it is implied by $n\ge2$ and $b_i>0$, which the instance model includes
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed pp. 15–16 (PDF pp. 16–17), definition of κ_δ and Proposition 4.1; proof printed pp. 16–18 (PDF pp. 17–19); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem proportional_aps_with_slack {n m : ℕ} (X : Instance n m) (hn : 2 ≤ n)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hδint : ∃ k : ℕ, 1 / δ = (k : ℝ))
    (hW : totalEntitlement X ≤ 1 - δ)
    (hb : ∀ i, X.entitlement i ≤ δ ^ 3 / (32768 * Real.log (8 / δ))) :
    ∃ D : FiniteLaw (Fin m → Fin n), ∀ i,
      X.entitlement i / totalEntitlement X * addVal (X.value i) Finset.univ ≤
        expectation D (fun σ => addVal (X.value i) (allocBundle σ i)) ∧
      ∀ σ, 0 < D.weight σ → target X i ≤ addVal (X.value i) (allocBundle σ i) := by sorry

end FairShareAlmostAll.Slack.Supplement
