-- Prove2me | Theorems.Thm_ConvexOptimization_weak_duality
-- name    : ConvexOptimization.weak_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:32:54.127+00:00
-- url     : https://prove2.me/theorems/af4d970d-f875-49fc-b9b7-bf0c8fa42b6e
-- title:
--   Weak duality
-- statement:
--   **Weak duality** — inequality (5.2) of Boyd & Vandenberghe: the dual function is a lower bound on the primal objective at every feasible point.
--
--   For the standard problem with objective $f_0$, inequality constraints $f_i(x) \le 0$ and equality constraints $\langle a_j,x\rangle = b_j$, write $L(x,\lambda,\nu) = f_0(x) + \sum_i \lambda_i f_i(x) + \sum_j \nu_j(\langle a_j,x\rangle - b_j)$ and $g(\lambda,\nu) = \inf_x L(x,\lambda,\nu)$. Let $\lambda \in \mathbb{R}^m$ with $\lambda_i \ge 0$ for all $i$, let $\nu \in \mathbb{R}^p$ be arbitrary, and let $x$ be feasible. Then
--
--   $$g(\lambda,\nu) \;\le\; f_0(x).$$
--
--   Taking the infimum over feasible $x$ gives $g(\lambda,\nu) \le p^{\star}$: every dual-feasible pair certifies a lower bound on the optimal value, at the cost of a single evaluation and with no convexity assumption on the problem. The difference $p^{\star} - g(\lambda,\nu)$ is the duality gap, and an equality $g(\lambda,\nu) = f_0(x)$ therefore proves simultaneously that $x$ is primal optimal and $(\lambda,\nu)$ dual optimal — the mechanism behind every statement later in this mission.
--
--   **Formalization Note** The inequality is between `EReal` values, so the vacuous case $g(\lambda,\nu) = -\infty$ needs no separate treatment; feasibility of $x$ is membership in the mission's feasible-set definition. Source: B&V §5.2.2, p. 225, eq. (5.2).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 225, §5.2.2 eq. (5.2) (weak duality)

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.weak_duality {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (lam : Fin mm → ℝ) (hlam : ∀ i, 0 ≤ lam i) (nu : Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ feasibleSet fc a b) :
    dualFunction f₀ fc a b lam nu ≤ (f₀ x : EReal) := by
  sorry
