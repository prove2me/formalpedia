-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_corollary
-- name    : BlackwellDiscreteDP.Stationary.corollary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:01:45.530949+00:00
-- url     : https://prove2.me/theorems/0b9422a6-01a3-482f-90d3-07f6abc0a46f
-- title:
--   Corollary (p. 721) — for each β ∈ [0, 1) some stationary policy is β-optimal
-- statement:
--   Fix $0\le\beta<1$. There is a decision rule $f\in F$ such that the stationary policy $f^{(\infty)}$ is $\beta$-optimal:
--
--   $$V_\beta(f^{(\infty)})\ge V_\beta(\pi)\qquad\text{for every policy }\pi,$$
--
--   where the comparison is coordinatewise and $\pi$ ranges over all policies, stationary or not.
--
--   Here "optimal" is meant at the fixed discount factor $\beta$ (the sense of §3). The same sentence in §4, with "optimal" meaning optimal for all $\beta$ near $1$, is Theorem 5.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 721, Corollary (to Theorem 3)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Corollary, p. 721 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"There is an optimal policy which is stationary."

Here "optimal" is the §3 notion at a fixed `β ∈ [0, 1)`: there is a decision rule `f` whose
stationary policy `f^(∞)` satisfies `V_β(f^(∞)) ≧ V_β(π)` for every policy `π` (deterministic,
Markov, possibly time-dependent). The §4 statement with the same words is Theorem 5. -/
theorem corollary {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ f : St → Act, M.IsBetaOptimal β (stationary f) := by sorry

end BlackwellDiscreteDP.Stationary
