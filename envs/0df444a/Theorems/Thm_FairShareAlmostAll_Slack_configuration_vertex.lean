-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_configuration_vertex
-- name    : FairShareAlmostAll.Slack.configuration_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:24.420988+00:00
-- url     : https://prove2.me/theorems/1100c824-85c0-45a0-bee4-a71137c4ef64
-- title:
--   A vertex exists in the defined finite configuration polytope
-- statement:
--   Under the Section 3 construction assumptions, the configuration polytope has a vertex:
--   $$\exists x\in\mathcal X:\quad x\text{ is not the midpoint of two distinct points of }\mathcal X.$$
--   This supporting obligation is the unnumbered vertex selection in Section 3.2. Vertex existence is a conclusion rather than a field in a structure or an assumed witness.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - generalization: W ≤ 1 − 8/q in Section 3 → W ≤ 1 − 15/(2q); reason: the same feasibility estimate W/(1−qc) ≤ 1−5/q holds; the remaining Section 3 arguments use feasibility and the unchanged cap, and every source instance satisfies this relaxed bound
--   - encoding: coordinates indexed by active agents and positive conditional support → total finite arrays with every unused coordinate constrained to zero; reason: zero extension is an affine bijection and preserves feasibility and midpoint vertexhood
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 11 (PDF p. 12), §3.2, unnumbered vertex selection paragraph; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets
import Definitions.Def_FairShareAlmostAll_Slack_ConfigurationPolytope

namespace FairShareAlmostAll.Slack

theorem configuration_vertex {n m : ℕ} (X : Instance n m) (q : ℕ) (h : SlackAssumptions X q)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (hD : ∀ i ∈ active X, certificate (X.value i) (X.entitlement i) (target X i) (D i)) :
    ∃ x : Fin n → Finset (Fin m) → ℝ, Vertex X q D x := by sorry

end FairShareAlmostAll.Slack
