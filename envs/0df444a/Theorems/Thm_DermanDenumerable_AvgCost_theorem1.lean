-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_theorem1
-- name    : DermanDenumerable.AvgCost.theorem1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:19:55.649534+00:00
-- url     : https://prove2.me/theorems/d4905747-6fe9-47bc-9111-1ab24e3fb885
-- title:
--   Theorem 1 — a bounded solution of (1) makes the minimizing rule of C'' optimal over C, with average cost g
-- statement:
--   Assume conditions (A) and (B): the state space $I$ is denumerable, each state $i$ has finitely many decisions, and the costs $w_{ik}$ are bounded. Suppose a number $g$ and a bounded set of numbers $\{v_j\}_{j \in I}$ satisfy
--   $$g + v_i = \min_k \Big\{ w_{ik} + \sum_{j\in I} q_{ij}(k) v_j \Big\}, \qquad i \in I. \tag{1}$$
--   Then a rule $R^* \in C''$ prescribing at each state $i$ a decision that minimizes the right side of (1) exists, and every such rule satisfies
--   $$g = Q_{R^*}(i) \le Q_R(i)$$
--   for every initial state $i$ and every rule $R \in C$ (history-dependent and randomized).
--
--   This is the verification theorem of the paper: a bounded solution of the average-cost optimality equation identifies the optimal average cost and an optimal stationary deterministic rule. Theorems 2, 3 and 4 all conclude by reducing to it.
--
--   **Formalization Note.** "R* is the rule which prescribes the decision that minimizes" is stated for every choice of minimizing decisions, as the proof allows ("if there are several minimizing decisions, let $k_i$ be any one of them"). The bounded $v$ is essential: on an infinite state space unbounded solutions of (1) do not certify optimality.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1548, Theorem 1

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), Theorem 1, p. 1548: under (A) and (B), if a bounded `{g, v_j}` solves (1), then a
rule `R* ∈ C''` prescribing at each state a decision minimizing the right side of (1) exists, and
every such rule satisfies `g = Q_{R*}(i) ≤ Q_R(i)` for every initial state `i` and every rule
`R ∈ C`. -/
theorem theorem1 {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (g : ℝ) (v : S → ℝ) (hv : BddFun v)
    (h1 : IsACOE M w g v) :
    (∃ e : StationaryPolicy M, IsMinimizer M w v e) ∧
      ∀ e : StationaryPolicy M, IsMinimizer M w v e →
        ∀ i : S, avgCostR e.toPolicy w i = g ∧ ∀ R : Policy M, g ≤ avgCostR R w i := by sorry

end DermanDenumerable.AvgCost
