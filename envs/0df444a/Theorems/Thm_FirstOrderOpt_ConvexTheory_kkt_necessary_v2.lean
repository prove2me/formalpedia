-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_kkt_necessary_v2
-- name    : FirstOrderOpt.ConvexTheory.kkt_necessary_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:16:16.675105+00:00
-- url     : https://prove2.me/theorems/ffd876e8-a270-45b1-a13d-f244312b6cd8
-- title:
--   Theorem 2.8(b) — KKT necessity under the restricted Slater condition (corrected sign)
-- statement:
--   Consider the convex program (2.3.16) $\min\{f(x): g_i(x)\le 0\ (i=1..m),\ h_j(x)=\langle w_j,x\rangle+b_j=0\ (j=1..p),\ x\in X\}$ with $X\subseteq\mathbb R^n$ closed convex and $f,g_i$ convex on $X$. Suppose the restricted Slater condition holds: there is $\bar x$ in the relative interior of $X$ with $g_i(\bar x)<0$ for all $i$ and $h_j(\bar x)=0$ for all $j$. If $x^*$ is an optimal solution at which $f$ and the $g_i$ are differentiable, then there exist multipliers $\lambda^*\ge 0$ and $y^*$ such that complementary slackness $\lambda^*_ig_i(x^*)=0$ holds and
--   $$-\Big(\nabla f(x^*)+\sum_i\lambda^*_i\nabla g_i(x^*)+\sum_jy^*_jw_j\Big)\in N_X(x^*),$$
--   where $N_X(x^*)=\{w:\langle w,y-x^*\rangle\le 0\ \forall y\in X\}$ is the normal cone (2.2.14), i.e. $0\in\nabla f(x^*)+\sum_i\lambda_i^*\nabla g_i(x^*)+\sum_jy_j^*w_j+N_X(x^*)$.
--
--   **Formalization Note.** The retired statement placed $+\nabla L(x^*)$ (the gradient of the Lagrangian) in the outward normal cone, which is the first-order condition of a *maximizer*; the accepted disproof is the one-dimensional instance $f=\langle v,\cdot\rangle$, $X=\{y:\langle v,y\rangle\ge 0\}$, $x^*=0$. The corrected statement places $-\nabla L(x^*)$ in $N_X(x^*)$, the standard stationarity condition. All other hypotheses (closed convex $X$, convexity, relative-interior Slater point, differentiability at $x^*$, feasibility and optimality of $x^*$) are as in the source; `normalCone` is the unchanged series definition.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 42, Theorem 2.8(b), with (2.2.14) for the normal cone

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

namespace FirstOrderOpt.ConvexTheory

open scoped Gradient

/-- Theorem 2.8(b) (KKT necessity under the restricted Slater condition), Lan p. 42. For the
convex program (2.3.16) `min f(x) s.t. g_i(x) ≤ 0, h_j(x) = ⟨w_j, x⟩ + b_j = 0, x ∈ X` with `X`
closed convex and `f, g_i` convex, suppose there is a point `x̄` in the relative interior of `X`
that is feasible with every inequality constraint strict. If `x*` is optimal and `f, g_i` are
differentiable at `x*`, then there exist multipliers `λ* ≥ 0`, `y*` with complementary slackness
`λ*_i g_i(x*) = 0` and the stationarity condition
`0 ∈ ∇f(x*) + Σ_i λ*_i ∇g_i(x*) + Σ_j y*_j w_j + N_X(x*)`, i.e.
`-(∇f(x*) + Σ_i λ*_i ∇g_i(x*) + Σ_j y*_j w_j) ∈ N_X(x*)` for the outward normal cone
`N_X(x*) = {w | ⟨w, y - x*⟩ ≤ 0 ∀ y ∈ X}` (2.2.14).

Corrected version: the retired statement put `+∇L(x*)` (instead of `-∇L(x*)`) into the outward
normal cone, which is the first-order condition of a *maximizer*. -/
theorem kkt_necessary_v2 {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (barx : EuclideanSpace ℝ (Fin n)) (hbarx_ri : barx ∈ intrinsicInterior ℝ X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hfdiff : DifferentiableAt ℝ f xstar) (hgdiff : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hxstar_g : ∀ i, g i xstar ≤ 0) (hxstar_h : ∀ j, h j xstar = 0)
    (hxstar_opt : ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x) :
    ∃ lamStar : Fin m → ℝ, ∃ yStar : Fin p → ℝ, (∀ i, 0 ≤ lamStar i) ∧
      -((∇ f xstar) + (∑ i, lamStar i • ∇ (g i) xstar) + (∑ j, yStar j • w j)) ∈
        normalCone X xstar ∧
      (∀ i, lamStar i * g i xstar = 0) := by sorry

end FirstOrderOpt.ConvexTheory
