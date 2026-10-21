-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_proposition_1_existence
-- name    : FollowCustomers.SmallCost.proposition_1_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:46.638794+00:00
-- url     : https://prove2.me/theorems/f4e0eb4a-bb4f-48bf-8c49-028be95d7b91
-- title:
--   Proposition 1, p. 14 (PDF 16) — existence of x̲, x* solving (14)–(15) for every small K > 0 (pinned reading)
-- statement:
--   Let $r,\sigma^2,\delta>0$. Then there is a solution branch of the threshold system: functions $K\mapsto\underline x(K)$ and $K\mapsto x^*(K)$ such that, for every sufficiently small $K>0$, the pair $(\underline x(K),x^*(K))$ solves equations (14) and (15) and lies in the region
--   $$\tfrac12<\underline x(K)<x^*(K)<1,\qquad \delta\,(2x^*(K)-1)<3 .$$
--
--   Proposition 1 of the paper states that, when the repositioning cost $K$ is not too large, the symmetric market equilibrium has thresholds $\underline x$ and $x^*$ obtained as solutions of (14)–(15). This item formalizes the existence of such solutions. It guarantees that the statements of the mission about every solution branch are not vacuous.
--
--   **Formalization Note.** "K is not too large" is pinned as "for every sufficiently small $K>0$". The hazard-rate part of Proposition 1 (equation (13)) and the verification that the thresholds form a Markov perfect equilibrium are not formalized.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), p. 14 (PDF 16), Proposition 1 (existence of solutions of (14)–(15), pinned reading)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- Proposition 1, existence part (pinned reading of "K not too large"): for every admissible
parameter tuple, the system (14)–(15) has a solution in the region for every sufficiently
small `K > 0`. -/
theorem proposition_1_existence (P : Params) (hP : P.Standing) :
    ∃ xl xs : ℝ → ℝ, IsBranch P xl xs := by sorry

end FollowCustomers.SmallCost
