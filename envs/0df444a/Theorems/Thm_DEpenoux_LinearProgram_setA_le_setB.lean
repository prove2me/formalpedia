-- Prove2me | Theorems.Thm_DEpenoux_LinearProgram_setA_le_setB
-- name    : DEpenoux.LinearProgram.setA_le_setB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:22:15.468303+00:00
-- url     : https://prove2.me/theorems/675d0fda-6fef-461c-9bca-09f86502e48e
-- title:
--   Section 5 — every point of $A$ lies componentwise below every point of $B$
-- statement:
--   In d'Epenoux's production–inventory model with stock levels $0,\dots,\sigma$, a stochastic kernel $p_{js}$, real costs $d_{ij}$ and discount $0 < \lambda < 1$, let $A$ be the set of vectors satisfying the constraints (9),
--   $$ U_{ij} = u_i - \lambda \sum_s p_{js} u_s - d_{ij} \le 0 \qquad (i \le j), $$
--   and $B$ the set of vectors with $\prod_{j \ge i} U_{ij} = 0$ for every $i$. If $u_a \in A$ and $u_b \in B$, then
--   $$ u_a \le u_b \quad \text{componentwise.} $$
--
--   In the paper this is the step "$u_b - u_a \ge 0$", from which $u^* = \max(u \in A)$ follows, since $u^*$ lies in both sets.
--
--   **Formalization Note** The order on vectors is the componentwise order of `Fin (σ + 1) → ℝ`.
-- source:
--   d'Epenoux, A Probabilistic Production and Inventory Problem, Management Sci. 10 (1963), p. 104, Section 5

import Mathlib
import Definitions.Def_DEpenoux_LinearProgram_Model

namespace DEpenoux.LinearProgram

theorem setA_le_setB (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∀ ua ∈ setA p d lam, ∀ ub ∈ setB p d lam, ua ≤ ub := by sorry

end DEpenoux.LinearProgram
