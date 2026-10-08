-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_theorem2
-- name    : DermanDenumerable.AvgCost.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:20:44.533808+00:00
-- url     : https://prove2.me/theorems/9daddc1f-000d-4678-8e90-7985241089b5
-- title:
--   Theorem 2 — under the conditions of Lemma 1, a rule optimal over C'' is optimal over C
-- statement:
--   Assume (A), (B) and (C), and let $R \in C''$ satisfy (D): a number $g$ and a bounded set of numbers $\{v_j\}$ solve (2) for $R$. If $R$ is optimal over $C''$, that is $Q_R(i) \le Q_{R'}(i)$ for every $R' \in C''$ and every $i$, then $R$ is optimal over $C$:
--   $$Q_R(i) \le Q_{R'}(i) \qquad \text{for every rule } R' \in C \text{ and every } i \in I.$$
--
--   Under the recurrence condition (C), stationary deterministic rules therefore cannot be beaten by history-dependent or randomized ones once they are best among themselves.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1550, Theorem 2

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), Theorem 2, p. 1550: under the conditions of Lemma 1 ((A), (B), (C), and (D) for
the rule `R = e ∈ C''` with a bounded `{g, v_j}`), if `R` is optimal over `C''` then it is optimal
over `C`. -/
theorem theorem2 {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (e : StationaryPolicy M) (g : ℝ)
    (v : S → ℝ) (hv : BddFun v) (hD : IsEvaluation M w e g v) :
    OptimalOverC'' w e → OptimalOverC w e.toPolicy := by sorry

end DermanDenumerable.AvgCost
