-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_serve_fractional_agents
-- name    : FairShareAlmostAll.Slack.serve_fractional_agents
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:39.004206+00:00
-- url     : https://prove2.me/theorems/9ceae060-ca5a-40e4-a172-8e8114396ae9
-- title:
--   Claim 3.4 — Serving the fractional agents
-- statement:
--   For the fractional set $F$ of any vertex of the configuration polytope, the reserve admits pairwise disjoint bundles satisfying
--   $$A_i\subseteq R,\qquad u_i(A_i)\ge1\quad(i\in F).$$
--   The original capped normalization and original entitlements are used. Agents outside $F$ receive empty bundles in this partial allocation, allowing disjoint recombination with Lemma 2.1.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - generalization: W ≤ 1 − 8/q in Section 3 → W ≤ 1 − 15/(2q); reason: the same feasibility estimate W/(1−qc) ≤ 1−5/q holds; the remaining Section 3 arguments use feasibility and the unchanged cap, and every source instance satisfies this relaxed bound
--   - encoding: coordinates indexed by active agents and positive conditional support → total finite arrays with every unused coordinate constrained to zero; reason: zero extension is an affine bijection and preserves feasibility and midpoint vertexhood
--   - encoding: bundles indexed by F → bundles indexed by all agents, empty outside F; reason: empty extension changes no allocation on F
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 12 (PDF p. 13), Claim 3.4; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets
import Definitions.Def_FairShareAlmostAll_Slack_ConfigurationPolytope

namespace FairShareAlmostAll.Slack

theorem serve_fractional_agents {n m : ℕ} (X : Instance n m) (q : ℕ) (h : SlackAssumptions X q)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (hD : ∀ i ∈ active X, certificate (X.value i) (X.entitlement i) (target X i) (D i))
    (x : Fin n → Finset (Fin m) → ℝ) (hx : Vertex X q D x) :
    ∃ A : Fin n → Finset (Fin m), PartialAllocation A ∧
      (∀ i, i ∉ fractionalAgents X q D x → A i = ∅) ∧
      ∀ i ∈ fractionalAgents X q D x, A i ⊆ reserve q m ∧ 1 ≤ cappedValue X i (A i) := by sorry

end FairShareAlmostAll.Slack
