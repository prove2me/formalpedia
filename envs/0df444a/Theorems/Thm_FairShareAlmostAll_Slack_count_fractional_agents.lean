-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_count_fractional_agents
-- name    : FairShareAlmostAll.Slack.count_fractional_agents
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:30.655794+00:00
-- url     : https://prove2.me/theorems/3313f122-9798-4204-a9a9-2909ee9f699b
-- title:
--   Claim 3.2 — Counting fractional agents
-- statement:
--   At any vertex $x$, let $F_z$ be the fractional agents with $b_i\ge z$. Every real threshold $0<z\le c$ satisfies both inequalities
--   $$|F_z|\le h(z)\le2+2q\log(1/z),\qquad h(z)=1+\left\lceil\frac{\log(1/z)}{\log(1+1/q)}\right\rceil.$$
--   The vertex is taken in the defined configuration polytope; it is not an arbitrary sparse array. The logarithmic coefficient remains exactly $2q$.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - generalization: W ≤ 1 − 8/q in Section 3 → W ≤ 1 − 15/(2q); reason: the same feasibility estimate W/(1−qc) ≤ 1−5/q holds; the remaining Section 3 arguments use feasibility and the unchanged cap, and every source instance satisfies this relaxed bound
--   - encoding: coordinates indexed by active agents and positive conditional support → total finite arrays with every unused coordinate constrained to zero; reason: zero extension is an affine bijection and preserves feasibility and midpoint vertexhood
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 11 (PDF p. 12), Claim 3.2; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets
import Definitions.Def_FairShareAlmostAll_Slack_ConfigurationPolytope

namespace FairShareAlmostAll.Slack

theorem count_fractional_agents {n m : ℕ} (X : Instance n m) (q : ℕ) (h : SlackAssumptions X q)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (hD : ∀ i ∈ active X, certificate (X.value i) (X.entitlement i) (target X i) (D i))
    (x : Fin n → Finset (Fin m) → ℝ) (hx : Vertex X q D x)
    (z : ℝ) (hz : 0 < z) (hzc : z ≤ cap q) :
    (fractionalAbove X q D x z).card ≤ thresholdIndex q z ∧
    (thresholdIndex q z : ℝ) ≤ 2 + 2 * (q : ℝ) * Real.log (1 / z) := by sorry

end FairShareAlmostAll.Slack
