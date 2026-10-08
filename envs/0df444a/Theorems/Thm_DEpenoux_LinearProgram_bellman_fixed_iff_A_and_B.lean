-- Prove2me | Theorems.Thm_DEpenoux_LinearProgram_bellman_fixed_iff_A_and_B
-- name    : DEpenoux.LinearProgram.bellman_fixed_iff_A_and_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:22:11.794771+00:00
-- url     : https://prove2.me/theorems/e2cf5a0c-d498-4f11-b4fd-e20e956daf9a
-- title:
--   Section 5 — (7) holds iff $u\in A$ and $u\in B$; the points of $B$ are the costs of the strategies
-- statement:
--   In d'Epenoux's production–inventory model with stock levels $0,\dots,\sigma$, a stochastic kernel $p_{js}$, real costs $d_{ij}$ and discount $0 < \lambda < 1$, let $T$ be the Bellman operator
--   $$ (Tu)_i = \min_{j \ge i} \Big( d_{ij} + \lambda \sum_s p_{js} u_s \Big), $$
--   and let $U_{ij} = u_i - \lambda \sum_s p_{js} u_s - d_{ij}$. Then:
--
--   1. a vector $u$ solves (7), $Tu = u$, if and only if $u \in A$ and $u \in B$, that is, $U_{ij} \le 0$ for every $i$ and every admissible $j \ge i$, and $\prod_{j \ge i} U_{ij} = 0$ for every $i$;
--   2. a vector $u$ lies in $B$ if and only if it is the cost of some strategy: there is a map $J$ with $i \le J(i)$ for all $i$ such that
--   $$ u_i = d_{i J(i)} + \lambda \sum_s p_{J(i) s} u_s \qquad (i = 0, \dots, \sigma), $$
--   i.e. $u = d_J + \lambda P_J u$, the system (2).
--
--   This is the decomposition with which Section 5 turns the dynamic program (7) into a linear program: (A) are the linear constraints (9), and (B) selects the strategy costs.
--
--   **Formalization Note** The page writes "$\max_j U_{ij} = 0$" and "$\Pi_j U_{ij} = 0$"; here $j$ ranges over the admissible potentials $j \ge i$, as in the paper's count of $\tfrac12(\sigma+1)(\sigma+2)$ constraints. "The points of the set $B$ correspond to the costs associated with every possible strategy" is formalized as the equivalence in item 2, with the cost of $J$ described as a solution of (2) through the policy operator `BertsekasDiscountedPolicyOp`.
-- source:
--   d'Epenoux, A Probabilistic Production and Inventory Problem, Management Sci. 10 (1963), p. 104, Section 5 (decomposition of (7) into (A) and (B))

import Mathlib
import Definitions.Def_DEpenoux_LinearProgram_Model

namespace DEpenoux.LinearProgram

theorem bellman_fixed_iff_A_and_B (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (∀ u : Fin (σ + 1) → ℝ,
      BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u = u ↔
        u ∈ setA p d lam ∧ u ∈ setB p d lam) ∧
    (∀ u : Fin (σ + 1) → ℝ,
      u ∈ setB p d lam ↔
        ∃ J : Fin (σ + 1) → Fin (σ + 1), IsStrategy J ∧
          BertsekasDiscountedPolicyOp (model σ p d hp0 hp1) lam J u = u) := by sorry

end DEpenoux.LinearProgram
