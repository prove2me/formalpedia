-- Prove2me | Theorems.Thm_ConvexOptimization_kkt_sufficient_for_convex
-- name    : ConvexOptimization.kkt_sufficient_for_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:34:58.298012+00:00
-- url     : https://prove2.me/theorems/458968c2-bf7b-421c-94fb-0a282deed486
-- title:
--   KKT sufficiency for convex problems
-- statement:
--   **The KKT conditions are sufficient for optimality in a convex problem** — no constraint qualification needed.
--
--   Let $f_0$ and $f_1,\dots,f_m$ be convex and differentiable on $\mathbb{R}^n$, with gradient fields $\nabla f_0$ and $\nabla f_i$, and consider the constraints $f_i(x) \le 0$ and $\langle a_j,x\rangle = b_j$. Suppose the triple $(x^{\star},\lambda,\nu)$ satisfies the KKT conditions:
--
--   $$f_i(x^{\star}) \le 0, \qquad \langle a_j,x^{\star}\rangle = b_j, \qquad \lambda_i \ge 0, \qquad \lambda_i f_i(x^{\star}) = 0, \qquad \nabla f_0(x^{\star}) + \sum_{i}\lambda_i\nabla f_i(x^{\star}) + \sum_{j}\nu_j a_j = 0 .$$
--
--   Then $x^{\star}$ is feasible and minimizes $f_0$ over the feasible set.
--
--   This is the easy half of the KKT characterization, and the half that needs no Slater point: whenever a solver returns a primal–dual triple satisfying these equations, optimality is certified outright. The convexity hypotheses enter only through the fact that the stationarity condition makes $x^{\star}$ a global minimizer of the convex function $L(\cdot,\lambda,\nu)$.
--
--   **Formalization Note** The hypotheses are packaged in the mission's `IsKKTPoint` predicate; the gradient fields are explicit arguments tied to $f_0$, $f_i$ by `HasGradientAt`, and convexity is stated on `Set.univ` because the problem is in total-function form. The conclusion is a conjunction of feasibility and `IsMinOn`. Source: B&V §5.5.3, p. 244.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 244, §5.5.3 eq. (5.49) (KKT conditions for convex problems: sufficiency, no constraint qualification needed)

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality
import Definitions.Def_ConvexOptimization_IsKKTPoint

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.kkt_sufficient_for_convex {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (f₀' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf₀' : ∀ x, HasGradientAt f₀ (f₀' x) x)
    (fc' : Fin mm → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hfc' : ∀ i x, HasGradientAt (fc i) (fc' i x) x)
    (xs : EuclideanSpace ℝ (Fin n)) (lam : Fin mm → ℝ) (nu : Fin p → ℝ)
    (hkkt : IsKKTPoint fc a b f₀' fc' xs lam nu) :
    xs ∈ feasibleSet fc a b ∧ IsMinOn f₀ (feasibleSet fc a b) xs := by
  sorry
