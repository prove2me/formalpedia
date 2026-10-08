-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_kkt_sufficient_v2
-- name    : FirstOrderOpt.ConvexTheory.kkt_sufficient_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:16:14.162157+00:00
-- url     : https://prove2.me/theorems/af191e75-29a3-4591-a7d4-6b6f4857f397
-- title:
--   Theorem 2.8(a) — KKT sufficiency (corrected sign)
-- statement:
--   Consider the convex program (2.3.16) with $X\subseteq\mathbb R^n$ convex and $f,g_i$ convex on $X$, and let $x^*\in X$ be feasible ($g_i(x^*)\le 0$, $h_j(x^*)=0$) with $f,g_i$ differentiable at $x^*$. If there are multipliers $\lambda^*\ge 0$ and $y^*$ with $\lambda^*_ig_i(x^*)=0$ for all $i$ and
--   $$-\Big(\nabla f(x^*)+\sum_i\lambda^*_i\nabla g_i(x^*)+\sum_jy^*_jw_j\Big)\in N_X(x^*),$$
--   then $x^*$ is an optimal solution: $f(x^*)\le f(x)$ for every feasible $x$.
--
--   **Formalization Note.** The source writes the stationarity condition with the dual (starred) cone $N_X^*(x^*)$, which is $-N_X(x^*)$ for the outward normal cone $N_X$ of (2.2.14); the retired statement mapped it onto the unstarred cone, i.e. flipped the sign and certified a maximizer of the linearized Lagrangian (disproved). The corrected hypothesis is $-\nabla L(x^*)\in N_X(x^*)$. Everything else is as in the source.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 42, Theorem 2.8(a)

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

namespace FirstOrderOpt.ConvexTheory

open scoped Gradient

/-- Theorem 2.8(a) (KKT sufficiency), Lan p. 42. For the convex program (2.3.16) with `X`
convex and `f, g_i` convex, let `x*` be feasible with `f, g_i` differentiable at `x*`. If there
are multipliers `λ* ≥ 0`, `y*` with complementary slackness `λ*_i g_i(x*) = 0` and the
stationarity condition `0 ∈ ∇f(x*) + Σ_i λ*_i ∇g_i(x*) + Σ_j y*_j w_j + N_X(x*)`, i.e.
`-(∇f(x*) + Σ_i λ*_i ∇g_i(x*) + Σ_j y*_j w_j) ∈ N_X(x*)` for the outward normal cone (2.2.14),
then `x*` is optimal.

Corrected version: the retired statement put `+∇L(x*)` into the outward normal cone (the
source's starred cone `N_X^*(x*)` is the polar `-N_X(x*)`), which certifies a maximizer of the
linearized Lagrangian, not a minimizer. -/
theorem kkt_sufficient_v2 {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hfdiff : DifferentiableAt ℝ f xstar) (hgdiff : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hxstar_g : ∀ i, g i xstar ≤ 0) (hxstar_h : ∀ j, h j xstar = 0)
    (lamStar : Fin m → ℝ) (yStar : Fin p → ℝ) (hlamStar : ∀ i, 0 ≤ lamStar i)
    (hstationarity :
      -((∇ f xstar) + (∑ i, lamStar i • ∇ (g i) xstar) + (∑ j, yStar j • w j)) ∈
        normalCone X xstar)
    (hcomplementary : ∀ i, lamStar i * g i xstar = 0) :
    ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x := by sorry

end FirstOrderOpt.ConvexTheory
