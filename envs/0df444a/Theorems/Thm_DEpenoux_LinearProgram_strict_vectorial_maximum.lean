-- Prove2me | Theorems.Thm_DEpenoux_LinearProgram_strict_vectorial_maximum
-- name    : DEpenoux.LinearProgram.strict_vectorial_maximum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:22:22.095047+00:00
-- url     : https://prove2.me/theorems/739b8c18-2234-4f92-8494-57c8b93c6534
-- title:
--   Section 5 — if every $P_J$ is indecomposable, $u^*$ is a strict vectorial maximum of $A$
-- statement:
--   In d'Epenoux's production–inventory model with stock levels $0,\dots,\sigma$, a stochastic kernel $p_{js}$, real costs $d_{ij}$ and discount $0 < \lambda < 1$, assume that for every strategy $J$ (every map with $i \le J(i)$) the transition matrix $(P_J)_{is} = p_{J(i)s}$ is indecomposable: for all $i, k$ there is $n \ge 0$ with $(P_J^n)_{ik} > 0$. Let $u^*$ be a solution of (7),
--   $$ u^*_i = \min_{j \ge i}\Big( d_{ij} + \lambda \sum_s p_{js} u^*_s \Big). $$
--   Then $u^*$ is a strict vectorial maximum of the constraint set $A$ of (9): for every $u \in A$ with $u \ne u^*$,
--   $$ u_i < u^*_i \qquad \text{for every } i. $$
--
--   This is the sufficient condition stated at the end of the strict-maximum paragraph of Section 5.
--
--   **Formalization Note** Only the sufficient condition ("it is sufficient that they form an indecomposable group with respect to all the transition matrices $P_J$") is formalized; the paper's necessary and sufficient condition in terms of $P_{J^*}$ is not, because it comes with no argument and its meaning when several strategies are optimal is unclear. "Indecomposable group" is read as irreducibility of the matrix, as in (5).
-- source:
--   d'Epenoux, A Probabilistic Production and Inventory Problem, Management Sci. 10 (1963), p. 104, Section 5 (strict vectorial maximum), using Eq. (5), p. 100

import Mathlib
import Definitions.Def_DEpenoux_LinearProgram_Model

namespace DEpenoux.LinearProgram

theorem strict_vectorial_maximum (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hirr : ∀ J : Fin (σ + 1) → Fin (σ + 1), IsStrategy J →
      ∀ i k, ∃ n : ℕ, 0 < (stratMatrix p J ^ n) i k)
    (uStar : Fin (σ + 1) → ℝ)
    (huStar : BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam uStar = uStar)
    (u : Fin (σ + 1) → ℝ) (hu : u ∈ setA p d lam) (hne : u ≠ uStar) :
    ∀ i, u i < uStar i := by sorry

end DEpenoux.LinearProgram
