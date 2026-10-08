-- Prove2me | Theorems.Thm_ArapostathisAC_SennottACOI_theorem_5_9
-- name    : ArapostathisAC.SennottACOI.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:44:52.55032+00:00
-- url     : https://prove2.me/theorems/e81ecf7f-82b4-4ab7-8da4-cccac1204c41
-- title:
--   Theorem 5.9 — under Sennott's Assumptions 5.14–5.16 an AC-optimal stationary policy exists
-- statement:
--   Consider a controlled Markov process with countable state space $S=\{0,1,2,\dots\}$, nonempty compact admissible action sets $U(i)$, a nonnegative one-stage cost $c(i,a)$ and transition probabilities $P(j\mid i,a)$, with $c(i,\cdot)$ and $P(j\mid i,\cdot)$ continuous on $U(i)$. Let $J^*_\beta$ be the optimal $\beta$-discounted cost, $h_\beta(i)=J^*_\beta(i)-J^*_\beta(0)$, and suppose:
--
--   1. (Assumption 5.14) $J^*_\beta(i)<\infty$ for every $i\in S$ and $\beta\in(0,1)$;
--   2. (Assumption 5.15) there is a nonnegative integer $L$ with $h_\beta(i)\ge-L$ for all $i$ and $\beta$;
--   3. (Assumption 5.16) there is $M:S\to\mathbb R_+$ with $h_\beta(i)\le M(i)$ for all $i$ and $\beta$, and for each $i$ an action $a(i)\in U(i)$ with $\sum_jP(j\mid i,a(i))M(j)<\infty$.
--
--   Then there exists a stationary deterministic policy $f\in\Pi_{SD}$ that is **AC-optimal**:
--   $$J(i,f)=\limsup_{N\to\infty}\frac1N E^f_i\sum_{t=0}^{N-1}c(X_t,A_t)=\inf_{\pi\in\Pi}J(i,\pi)=J^*(i)\qquad\text{for every }i\in S,$$
--   the infimum ranging over all admissible policies, history dependent and randomized.
--
--   This is Sennott's existence theorem for average-cost optimal stationary policies with unbounded costs, in the form surveyed by Arapostathis et al.; it requires no bounded solution of the average cost optimality equation, only the one-sided conditions above.
--
--   **Formalization Note** The average costs are $\limsup$s in $[0,\infty]$ and the optimal average cost is the infimum over the class $\Pi$ of all admissible policies. Assumptions 5.14–5.16 are the definitions `Assumption5_14`, `Assumption5_15`, `Assumption5_16`; the differential value $h_\beta$ is used only together with Assumption 5.14, so it is never read off an infinite $J^*_\beta$. The proof also shows that $J(i,f)=J^*(i)$ is a constant $\rho^*$ and that $f$ attains an average cost optimality inequality; these are stated in the milestones, not in this goal.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 308, Theorem 5.9 (Assumptions 5.14–5.16, p. 307)

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Theorem 5.9 (p. 308): under Assumptions 5.14–5.16 there exists an AC-optimal stationary
deterministic policy `f ∈ Π_SD`, i.e. `J(i, f) = J*(i) = inf_{π ∈ Π} J(i, π)` for every state
`i`, the infimum ranging over all admissible (history-dependent, randomized) policies. -/
theorem theorem_5_9 (M : ArapostathisAC.VanishingDiscount.CMP A) (h14 : Assumption5_14 M) (h15 : Assumption5_15 M)
    (h16 : Assumption5_16 M) :
    ∃ f : StationaryPolicy M, ArapostathisAC.VanishingDiscount.IsAvgOptimal M f := by sorry

end ArapostathisAC.SennottACOI
