-- Prove2me | Theorems.Thm_ErrBoundQG_ProxLin_eq_5_2
-- name    : ErrBoundQG.ProxLin.eq_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:35.200439+00:00
-- url     : https://prove2.me/theorems/cc49b2a2-4530-4240-9b0c-b3a78bea5c05
-- title:
--   (5.2), p. 14 — quadratic approximation error of the linearized composite objective
-- statement:
--   For $\varphi=g+h\circ c$, suppose that $h$ is $L$-Lipschitz and the Jacobian of $c$ is $\beta$-Lipschitz. For all $x,y\in\mathbb R^n$, the linearization error satisfies
--
--   $$
--   -\frac{L\beta}{2}\|x-y\|^2\le
--   h(c(y))-h(c(x)+\nabla c(x)(y-x))\le
--   \frac{L\beta}{2}\|x-y\|^2.
--   $$
--
--   This gives the second-order comparison used to estimate prox-linear steps.
--
--   **Formalization Note** The equation is stated for the finite $h$ terms. In the paper's expression $\varphi(y)-\varphi(x;y)$, both terms can equal $+\infty$ when $g(y)=+\infty$, making their difference undefined.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 14, (5.2)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

namespace ErrBoundQG.ProxLin

theorem eq_5_2 {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hhL : ∀ a b, |h a - h b| ≤ L * ‖a - b‖)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (x y : En n) :
    -(L * β / 2) * ‖x - y‖ ^ 2 ≤
        h (c y) - h (c x + fderiv ℝ c x (y - x)) ∧
    h (c y) - h (c x + fderiv ℝ c x (y - x)) ≤
        L * β / 2 * ‖x - y‖ ^ 2 := by sorry

end ErrBoundQG.ProxLin
