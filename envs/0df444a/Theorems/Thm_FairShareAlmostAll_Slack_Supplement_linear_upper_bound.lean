-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_linear_upper_bound
-- name    : FairShareAlmostAll.Slack.Supplement.linear_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:16:48.898453+00:00
-- url     : https://prove2.me/theorems/ece67783-491d-47d8-9817-890054a194f4
-- title:
--   Theorem 4 — Linear upper bound $c^\star(\varepsilon)\le13\varepsilon$
-- statement:
--   Let $c^\star(\varepsilon)$ be the supremum of the numbers $c\in[0,1]$ such that every additive instance satisfying
--
--   $$\sum_{i\in N}b_i<1-\varepsilon,\qquad 0<b_i\le c\quad(i\in N)$$
--
--   admits an allocation $(A_i)_{i\in N}$ with $v_i(A_i)\ge\mathrm{APS}_i(b_i)$ for every agent. Then for every small enough $\varepsilon>0$,
--
--   $$c^\star(\varepsilon)\le13\varepsilon.$$
--
--   That is, there is $\varepsilon_0>0$ such that the bound holds for all $0<\varepsilon<\varepsilon_0$. It complements Theorem 1: any entitlement cap guaranteeing APS allocations under slack $\varepsilon$ must be $O(\varepsilon)$, whereas Theorem 1 achieves order $\varepsilon^2/\log(1/\varepsilon)$.
--
--   **Formalization Note** The supremum is over the definition `cStar`, whose admissible caps quantify over all instances with $n\ge2$ agents (the paper's model); excluding $n=0$ prevents an empty admissible set. The threshold $\varepsilon_0$ is existential, as "small enough" states; the paper's proof gives $\varepsilon_0=1/51$.
--
--   Differences from the source:
--   - encoding: an allocation $(A_i)_{i\in N}$ (partial or complete) in the defining property of $c^\star(\varepsilon)$ → a complete map $\sigma$ from goods to agents in `CapAdmissible`; reason: by nonnegativity a partial allocation meeting every APS can be completed without decreasing any value, so the admissible caps are the same
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 5 (PDF p. 6), Theorem 4; proof printed p. 22 (PDF p. 23); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_FairShareAlmostAll_Slack_Supplement_EntitlementCap

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem linear_upper_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → cStar ε ≤ 13 * ε := by sorry

end FairShareAlmostAll.Slack.Supplement
