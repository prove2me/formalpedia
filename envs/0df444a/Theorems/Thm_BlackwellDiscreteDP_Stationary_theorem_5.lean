-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_theorem_5
-- name    : BlackwellDiscreteDP.Stationary.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:02:09.764416+00:00
-- url     : https://prove2.me/theorems/46d39c05-431d-44f5-b0a0-d8d7c203e2d8
-- title:
--   Theorem 5 — there is a stationary policy that is β-optimal for all β sufficiently near 1
-- statement:
--   In every finite decision problem (finitely many states, a finite set of actions, real incomes $i(s,a)$ and transition probabilities $q(s'\mid s,a)$), there is a decision rule $f$ and a number $\beta_0<1$ such that
--
--   $$V_\beta(f^{(\infty)})\ge V_\beta(\pi)\qquad\text{for every }\beta\in(\beta_0,1)\text{ and every policy }\pi,$$
--
--   the comparison being coordinatewise and $\pi$ ranging over all policies $\{f_n\}$, stationary or not. In Blackwell's words: there is an optimal policy which is stationary, where "optimal" means $\beta$-optimal for all $\beta$ sufficiently near $1$ (today called Blackwell optimal).
--
--   One stationary policy and one threshold $\beta_0$ serve all discount factors in $(\beta_0,1)$ and all competitors at once. This is the starting point of the theory of sensitive discount optimality and of the treatment of the undiscounted case $\beta=1$ as a limit of discounted problems.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 725, Theorem 5

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Theorem 5, p. 725 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"There is an optimal policy which is stationary."

"Optimal" is the §4 notion (p. 721): β-optimal for all `β` sufficiently near `1`. One decision
rule `f` and one threshold `β₀ < 1` serve every `β ∈ (β₀, 1)` and every competing policy
`π` (deterministic, Markov, possibly time-dependent): `V_β(f^(∞)) ≧ V_β(π)` coordinatewise. -/
theorem theorem_5 {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act) :
    ∃ f : St → Act, M.IsOptimal (stationary f) := by sorry

end BlackwellDiscreteDP.Stationary
