-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_eq6_value_iteration_bound
-- name    : DermanDenumerable.AvgCost.eq6_value_iteration_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:19:56.24053+00:00
-- url     : https://prove2.me/theorems/9bd632e4-2250-4d65-9a90-3d07c003db4e
-- title:
--   (6) — a bounded solution of (1) keeps g_n(i) within a constant of ng + v_i
-- statement:
--   Under conditions (A) and (B), suppose a number $g$ and a bounded set of numbers $\{v_j\}_{j\in I}$ satisfy the optimality equation (1),
--   $$g + v_i = \min_k \Big\{ w_{ik} + \sum_{j\in I} q_{ij}(k) v_j \Big\}, \qquad i \in I.$$
--   Let $g_n(i)$ be the value iteration of (5): $g_0(i) = \min_k w_{ik}$ and $g_{n+1}(i) = \min_k \{ w_{ik} + \sum_{j} q_{ij}(k) g_n(j)\}$. Then there is a constant $C$ such that
--   $$n g + v_i - C \le g_n(i) \le n g + v_i + C, \qquad i \in I,\ n = 0, 1, 2, \dots$$
--
--   This is display (6) of the paper. Together with the finite-horizon optimality of $g_n$ it yields the lower bound $g \le Q_R(i)$ for every rule in the proof of Theorem 1.
--
--   **Formalization Note.** The paper calls the constant $M$; it is renamed $C$ because `M` names the model. The series $\sum_j q_{ij}(k) g_n(j)$ converges absolutely since $|g_n| \le (n+1)\sup|w|$.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1549, §3, displays (5) and (6)

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), §3, display (6), p. 1549: if `{g, v_j}` with `v` bounded solves (1), there is a
constant `C` (the paper's `M`) with `n g + v_i − C ≤ g_n(i) ≤ n g + v_i + C` for all `n` and `i`,
where `g_n` is defined by (5). -/
theorem eq6_value_iteration_bound {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (g : ℝ) (v : S → ℝ) (hv : BddFun v)
    (h1 : IsACOE M w g v) :
    ∃ C : ℝ, ∀ (n : ℕ) (i : S),
      (n : ℝ) * g + v i - C ≤ valueIter M w n i ∧ valueIter M w n i ≤ (n : ℝ) * g + v i + C := by sorry

end DermanDenumerable.AvgCost
