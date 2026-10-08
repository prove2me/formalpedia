-- Prove2me | Theorems.Thm_ErrBoundQG_ProxLin_lemma_5_1
-- name    : ErrBoundQG.ProxLin.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:35.112828+00:00
-- url     : https://prove2.me/theorems/20926ef9-5494-4652-a6d8-0198dc08135f
-- title:
--   Lemma 5.1, pp. 14–15 — gradient inequalities (5.3), (5.4), (5.5) for the prox-linear step
-- statement:
--   Consider the convex-composite problem $\min_x \varphi(x)=g(x)+h(c(x))$, where $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is proper, closed and convex, $h:\mathbb R^m\to\mathbb R$ is convex and $L$-Lipschitz, and $c:\mathbb R^n\to\mathbb R^m$ is $C^1$ with $\beta$-Lipschitz Jacobian $\nabla c$. For $x,y\in\mathbb R^n$ and $t>0$ let
--
--   $$
--   \varphi(x;y)=g(y)+h\big(c(x)+\nabla c(x)(y-x)\big),\qquad \varphi_t(x;y)=\varphi(x;y)+\tfrac{1}{2t}\|x-y\|^2,
--   $$
--
--   let $x^t$ be a minimizer of $\varphi_t(x;\cdot)$, and let $\mathcal G_t(x)=t^{-1}(x-x^t)$ be the prox-gradient. Then for every $y\in\mathbb R^n$:
--
--   1. $\displaystyle \varphi(x;y)\ \ge\ \varphi_t(x;x^t)+\langle \mathcal G_t(x),y-x\rangle+\tfrac t2\|\mathcal G_t(x)\|^2;$  (5.3)
--   2. $\displaystyle \varphi(y)\ \ge\ \varphi(x^t)+\langle \mathcal G_t(x),y-x\rangle+\tfrac t2(2-L\beta t)\|\mathcal G_t(x)\|^2-\tfrac{L\beta}{2}\|x-y\|^2;$  (5.4)
--   3. $\displaystyle \varphi(x)\ \ge\ \varphi(x^t)+\tfrac t2(2-L\beta t)\|\mathcal G_t(x)\|^2.$  (5.5)
--
--   These inequalities are the basic descent estimates for the prox-linear method: (5.5) shows that a step of length $\|\mathcal G_t(x)\|$ decreases the objective by an amount proportional to its square when $t<2/(L\beta)$.
--
--   **Formalization Note** Values of $\varphi$, $\varphi(x;\cdot)$ and $\varphi_t(x;\cdot)$ lie in $\mathbb R\cup\{\pm\infty\}$ (`EReal`); since $g$ never equals $-\infty$, each inequality is written with the real terms added on the smaller side, which is the paper's inequality where the left side is $+\infty$ and avoids $\infty-\infty$. The minimizer $x^t$ is a hypothesis `IsProxLinPoint g h c t x p` on a point $p$ rather than a chosen value. The lemma holds for every $t>0$; the Lipschitz constants $L,\beta\ge 0$ are needed only for (5.4) and (5.5).
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, pp. 14–15, Lemma 5.1, (5.3), (5.4), (5.5)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

namespace ErrBoundQG.ProxLin

open scoped InnerProductSpace

theorem lemma_5_1 {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hhL : ∀ a b, |h a - h b| ≤ L * ‖a - b‖)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (t : ℝ) (ht : 0 < t) (x p : En n)
    (hp : IsProxLinPoint g h c t x p) :
    (∀ y : En n,
      phiT g h c t x p +
          ((⟪t⁻¹ • (x - p), y - x⟫_ℝ + t / 2 * ‖t⁻¹ • (x - p)‖ ^ 2 : ℝ) : EReal) ≤
        phiLin g h c x y) ∧
    (∀ y : En n,
      phi g h c p +
          ((⟪t⁻¹ • (x - p), y - x⟫_ℝ + t / 2 * (2 - L * β * t) * ‖t⁻¹ • (x - p)‖ ^ 2
              - L * β / 2 * ‖x - y‖ ^ 2 : ℝ) : EReal) ≤
        phi g h c y) ∧
    phi g h c p + ((t / 2 * (2 - L * β * t) * ‖t⁻¹ • (x - p)‖ ^ 2 : ℝ) : EReal) ≤
      phi g h c x := by sorry

end ErrBoundQG.ProxLin
