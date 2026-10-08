-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_theorem_1
-- name    : BlackwellDiscreteDP.Stationary.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:01:22.27414+00:00
-- url     : https://prove2.me/theorems/79527a32-c256-4668-8c09-97d249d2fd36
-- title:
--   Theorem 1 — if π* ≧ (f, π*) for all f ∈ F, then π* is β-optimal
-- statement:
--   Fix $0\le\beta<1$ and a policy $\pi^*$ (not necessarily stationary). If no one-day deviation improves on $\pi^*$, that is,
--
--   $$V_\beta(f,\pi^*)\le V_\beta(\pi^*)\qquad\text{for every decision rule } f\in F,$$
--
--   then $\pi^*$ is $\beta$-optimal: $V_\beta(\pi^*)\ge V_\beta(\pi)$ coordinatewise for every policy $\pi$.
--
--   This is the verification principle of discounted dynamic programming; it reduces optimality against all (time-dependent) policies to a finite check over $F$.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 720, Theorem 1

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Theorem 1, p. 720 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"If π* ≧ (f, π*) for all f ε F, then π* is optimal."

Here "optimal" is the §3 notion at the fixed discount factor `β ∈ [0, 1)`: `V_β(π*) ≧ V_β(π)`
for every policy `π` (`IsBetaOptimal`). `π*` is an arbitrary policy, not necessarily
stationary. -/
theorem theorem_1 {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (πstar : Policy St Act)
    (h : ∀ f : St → Act, M.V β (Policy.cons f πstar) ≤ M.V β πstar) :
    M.IsBetaOptimal β πstar := by sorry

end BlackwellDiscreteDP.Stationary
