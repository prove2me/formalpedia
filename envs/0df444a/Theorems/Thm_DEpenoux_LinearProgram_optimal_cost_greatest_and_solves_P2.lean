-- Prove2me | Theorems.Thm_DEpenoux_LinearProgram_optimal_cost_greatest_and_solves_P2
-- name    : DEpenoux.LinearProgram.optimal_cost_greatest_and_solves_P2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:22:34.812844+00:00
-- url     : https://prove2.me/theorems/44319b0f-4a73-446d-ae84-a674d62d2ac2
-- title:
--   Section 5 and $(P_2)$ — $u^*=\max(u\in A)$, and $u^*$ is the unique optimal solution of $(P_2)$
-- statement:
--   Consider d'Epenoux's production–inventory model: stock levels $i = 0, 1, \dots, \sigma$; admissible potentials $j$ with $i \le j \le \sigma$; for each potential $j$ a probability vector $(p_{js})_{s}$ of end-of-period stocks; real one-period costs $d_{ij}$; and a discount factor $0 < \lambda < 1$. The fundamental equation (7) is
--   $$ u^*_i = \min_{j \ge i}\Big( d_{ij} + \lambda \sum_{s=0}^{\sigma} p_{js} u^*_s \Big) \qquad (i = 0, \dots, \sigma), $$
--   and $A$ is the set of vectors $u$ satisfying the constraints (9),
--   $$ U_{ij} = u_i - \lambda \sum_s p_{js} u_s - d_{ij} \le 0 \qquad (i \le j). $$
--   Then:
--
--   1. the system (7) has a solution;
--   2. every solution $u^*$ of (7) is the greatest element of $A$: $u^* \in A$, and every $u \in A$ satisfies $u \le u^*$ componentwise ("$u^* = \max(u \in A)$", p. 104);
--   3. for every weight vector $c$ with $\sum_i c_i = 1$ and all $c_i > 0$, $u^*$ is an optimal solution of the linear program
--   $$ (P_2) \qquad \text{maximize } (1-\lambda)\sum_i c_i u_i \ \text{ under the constraints (9)}, $$
--   and it is the only optimal solution of $(P_2)$.
--
--   This is the transition from dynamic to linear programming of Section 5: the optimal discounted cost, obtained in Sections 3–4 by policy iteration or value iteration, is computed by a single linear program whose constraints are linear in $u$.
--
--   **Formalization Note** Equation (7) is stated through the Bellman operator `BertsekasDiscountedBellmanOp` of the model, whose minimum ranges over the admissible potentials. "$u^* = \max(u \in A)$" is read as `IsGreatest` in the componentwise order. The paper says that a weighted objective with positive weights gives "the complete solution", in contrast with maximizing a single $u_e$; this is formalized as uniqueness of the optimal solution of $(P_2)$. The factor $1-\lambda$ of the objective (the paper's "cost annuity per period") is kept. Existence of a solution of (7) is a conjunct, not a hypothesis.
-- source:
--   d'Epenoux, A Probabilistic Production and Inventory Problem, Management Sci. 10 (1963), p. 104, Section 5 (u* = max (u ε A)), and p. 105, Eq. (9) and (P2)

import Mathlib
import Definitions.Def_DEpenoux_LinearProgram_Model

namespace DEpenoux.LinearProgram

theorem optimal_cost_greatest_and_solves_P2 (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (∃ u : Fin (σ + 1) → ℝ, BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u = u) ∧
    ∀ uStar : Fin (σ + 1) → ℝ,
      BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam uStar = uStar →
        IsGreatest (setA p d lam) uStar ∧
        ∀ c : Fin (σ + 1) → ℝ, (∀ i, 0 < c i) → ∑ i, c i = 1 →
          IsP2Optimal p d lam c uStar ∧
          ∀ v : Fin (σ + 1) → ℝ, IsP2Optimal p d lam c v → v = uStar := by sorry

end DEpenoux.LinearProgram
