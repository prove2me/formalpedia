-- Prove2me | Theorems.Thm_AdamDyn_Rates_eq_7_13
-- name    : AdamDyn.Rates.eq_7_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:20.535172+00:00
-- url     : https://prove2.me/theorems/d9018f0e-3fd2-41db-a474-5a895da0ef70
-- title:
--   §7.4 ii), (7.13) — $w_\delta$ is absolutely continuous and decreases at the rate of the residual terms
-- statement:
--   Let $F$, $S$, $a$, $b$, $\varepsilon$ satisfy the hypotheses of Theorem 3.2 without the condition on $F(\mathcal S)$, let $z(t)=(x(t),m(t),v(t))$ be a global solution of the Adam ODE with initial condition $(x_0,0,0)$, and let $w_\delta(t)=\tilde W_\delta(t,z(t))$ with $\tilde W_\delta$ as in (7.11). Then:
--
--   1. for every $\delta>0$ the function $w_\delta$ is absolutely continuous on $[1,+\infty)$, that is, on every compact interval $[1,T]$;
--   2. there exist $\delta>0$ and $c_2>0$ such that for almost every $t\ge1$, $w_\delta$ is differentiable at $t$ and
--
--   $$\frac{d}{dt}w_\delta(t)\ \le\ -c_2\Big(\|m(t)\|^2+\|\nabla F(x(t))\|^2+\|S(x(t))-v(t)\|^2\Big).$$
--
--   This is the decay half of the Łojasiewicz argument: $w_\delta$ is non-increasing on $[1,\infty)$ and its derivative controls the gradient and the two auxiliary residuals.
--
--   **Formalization Note** "Almost every" refers to Lebesgue measure on $\mathbb R$. The constants $\delta$ and $c_2$ may depend on $x_0$ and on the trajectory; they are quantified after the trajectory. Absolute continuity on the half-line is read as absolute continuity on each bounded interval $[1,T]$ (Mathlib's `AbsolutelyContinuousOnInterval`); without it an almost-everywhere derivative bound would say nothing about $w_\delta$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 20, §7.4 step ii), Eq. (7.13)

import Mathlib
import Definitions.Def_AdamDyn_Rates_AdamField
import Definitions.Def_AdamDyn_Rates_Lyapunov

open Filter Topology MeasureTheory

namespace AdamDyn.Rates

/-- Eq. (7.13), §7.4 step ii) (Barakat–Bianchi, p. 20): along the global solution `z` from
`(x0, 0, 0)`, every `w_δ` is absolutely continuous on `[1, +∞)` (on every compact interval
`[1, T]`, `T ≥ 1`), and there exist `δ > 0`, `c2 > 0` such that for almost every `t ≥ 1`, `w_δ` is
differentiable at `t` and
`(d/dt) w_δ(t) ≤ −c2 (‖m(t)‖² + ‖∇F(x(t))‖² + ‖S(x(t)) − v(t)‖²)`. -/
theorem eq_7_13 {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d))
    (z : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (EuclideanSpace ℝ (Fin d))) atTop)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hz : IsGlobalSolution F S a b ε x0 z) :
    (∀ δ > 0, ∀ T ≥ (1 : ℝ), AbsolutelyContinuousOnInterval (wδ F S a b ε δ z) 1 T) ∧
      ∃ δ > 0, ∃ c2 > 0, ∀ᵐ t ∂(volume : Measure ℝ), 1 ≤ t →
        DifferentiableAt ℝ (wδ F S a b ε δ z) t ∧
          deriv (wδ F S a b ε δ z) t ≤
            -c2 * (‖(z t).2.1‖ ^ 2 + ‖gradient F (z t).1‖ ^ 2 +
              ‖S (z t).1 - (z t).2.2‖ ^ 2) := by sorry

end AdamDyn.Rates
