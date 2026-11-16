-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_small_entitlement_family
-- name    : FairShareAlmostAll.Slack.Supplement.small_entitlement_family
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:16:17.113795+00:00
-- url     : https://prove2.me/theorems/30dbc315-1efb-4601-b728-3f071cffac91
-- title:
--   Proposition 5.1 — A family with arbitrarily small entitlements and no APS allocation
-- statement:
--   For every integer $n\ge5$ define
--
--   $$\beta_n=\frac{10}{10n+1}.$$
--
--   There is an instance with agent set $N=\{1,\dots,n\}$, finitely many goods, identical nonnegative additive valuations and entitlements $b_i=\beta_n$ for every agent, such that
--
--   $$\sum_{i\in N}b_i=1-\frac{1}{10n+1},\qquad \mathrm{APS}_i(\beta_n)\ge153\quad(i\in N),$$
--
--   but no allocation gives every agent value at least $153$.
--
--   Since $\beta_n\to0$ while the total entitlement stays below one, no entitlement cap of order larger than the slack can guarantee APS allocations; Theorem 4 is a direct consequence.
--
--   **Formalization Note** "No allocation" ranges over all partial allocations (pairwise disjoint bundles), which covers complete ones. The APS is the published `target` at the original entitlement.
--
--   Differences from the source:
--   - encoding: agent set $\{1,\dots,n\}$ and a finite good set → `Fin n` and `Fin m` with $m$ existentially chosen; reason: relabeling only
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 21 (PDF p. 22), Proposition 5.1; proof printed pp. 21–22 (PDF pp. 22–23); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem small_entitlement_family (n : ℕ) (hn : 5 ≤ n) :
    ∃ (m : ℕ) (X : Instance n m),
      (∀ i k, X.value i = X.value k) ∧
      (∀ i, X.entitlement i = 10 / (10 * (n : ℝ) + 1)) ∧
      totalEntitlement X = 1 - 1 / (10 * (n : ℝ) + 1) ∧
      (∀ i, 153 ≤ target X i) ∧
      ∀ A : Fin n → Finset (Fin m), PartialAllocation A →
        ∃ i, addVal (X.value i) (A i) < 153 := by sorry

end FairShareAlmostAll.Slack.Supplement
