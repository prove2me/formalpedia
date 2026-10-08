-- Prove2me | Theorems.Thm_ErrBoundQG_ProxLin_eq_5_6
-- name    : ErrBoundQG.ProxLin.eq_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:48.666981+00:00
-- url     : https://prove2.me/theorems/2d77e101-515d-49f2-93fc-6d95bd1c89d9
-- title:
--   (5.6), p. 15 (stated at t = 1/(Lβ)) — functional decrease of one prox-linear step
-- statement:
--   Consider the convex-composite problem $\min_x \varphi(x)=g(x)+h(c(x))$, where $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is proper, closed and convex, $h:\mathbb R^m\to\mathbb R$ is convex and $L$-Lipschitz, and $c:\mathbb R^n\to\mathbb R^m$ is $C^1$ with $\beta$-Lipschitz Jacobian, with $L,\beta>0$. Set the step size $t=1/(L\beta)$. If $x_{k+1}=x_k^t$ is the minimizer of the prox-linear subproblem $y\mapsto g(y)+h(c(x_k)+\nabla c(x_k)(y-x_k))+\frac1{2t}\|y-x_k\|^2$, then
--
--   $$
--   \varphi(x_{k+1})\ \le\ \varphi(x_k)-\frac{1}{2L\beta}\,\|\mathcal G_t(x_k)\|^2,\qquad \mathcal G_t(x_k)=t^{-1}(x_k-x_{k+1}).
--   $$
--
--   This is the per-iteration decrease guarantee of the prox-linear method (Algorithm 1 without backtracking), from which the paper derives its global $O(1/k)$ rate for $\min_i\|\mathcal G_t(x_i)\|^2$.
--
--   **Formalization Note** The page sets "$t\le 1/(L\beta)$" before (5.6), but (5.6) follows from (5.5) only at $t=1/(L\beta)$: for smaller $t$, (5.5) gives the decrease $\frac t2(2-L\beta t)\|\mathcal G_t(x_k)\|^2$, which is smaller than $\frac1{2L\beta}\|\mathcal G_t(x_k)\|^2$. The printed range is in fact too wide: with $c(x)=x^2/2$, $h(r)=r$, $g=0$ on $\mathbb R$ ($L=\beta=1$) the step is $x_{k+1}=(1-t)x_k$ and the decrease is $\frac{2t-t^2}{2}x_k^2<\frac12 x_k^2$ for every $t<1$. The statement is therefore made at $t=1/(L\beta)$, with $L,\beta>0$ so that $t$ is defined. The inequality is written additively in $\mathbb R\cup\{\pm\infty\}$ (it is trivial when $\varphi(x_k)=+\infty$). The iterate $x_{k+1}$ is a hypothesis `IsProxLinPoint` rather than a chosen value.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 15, (5.6)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

namespace ErrBoundQG.ProxLin

theorem eq_5_6 {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (L β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (hhL : ∀ a b, |h a - h b| ≤ L * ‖a - b‖)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (t : ℝ) (htLβ : t = (L * β)⁻¹) (xk xk1 : En n)
    (hstep : IsProxLinPoint g h c t xk xk1) :
    phi g h c xk1 +
        ((1 / (2 * L * β) * ‖t⁻¹ • (xk - xk1)‖ ^ 2 : ℝ) : EReal) ≤
      phi g h c xk := by sorry

end ErrBoundQG.ProxLin
