-- Prove2me | Theorems.Thm_ErrBoundQG_ProxLin_theorem_5_3
-- name    : ErrBoundQG.ProxLin.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:34.399005+00:00
-- url     : https://prove2.me/theorems/c3377a41-0bc2-4f54-ab06-931effcb5943
-- title:
--   Theorem 5.3, p. 16 — a prox-linear step yields a nearby nearly stationary point
-- statement:
--   Suppose that $h$ is $L$-Lipschitz and the Jacobian of $c$ is $\beta$-Lipschitz. For any $x$, $t>0$, and prox-linear point $x^t$, there is $\hat x$ with
--
--   $$
--   \|x^t-\hat x\|\le\|x^t-x\|,\qquad
--   \varphi(\hat x)-\varphi(x^t)\le\frac t2(L\beta t+1)\|\mathcal G_t(x)\|^2,
--   $$
--   $$
--   \operatorname{dist}(0,\partial\varphi(\hat x))\le
--   (3L\beta t+2)\|\mathcal G_t(x)\|.
--   $$
--
--   This connects the computable prox-linear step to a near-stationarity certificate at a nearby point.
--
--   **Formalization Note** The value inequality is written additively in extended reals, since $\varphi$ may equal $+\infty$ outside the domain of $g$. The distance upper bound is expressed by existence of a subgradient with the stated norm; this subdifferential is closed, so the distance is attained.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 16, Theorem 5.3

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

namespace ErrBoundQG.ProxLin

theorem theorem_5_3 {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hhL : ∀ a b, |h a - h b| ≤ L * ‖a - b‖)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (t : ℝ) (ht : 0 < t) (x p : En n)
    (hp : IsProxLinPoint g h c t x p) :
    ∃ xhat : En n,
      ‖p - xhat‖ ≤ ‖p - x‖ ∧
      phi g h c xhat ≤ phi g h c p +
        ((t / 2 * (L * β * t + 1) * ‖t⁻¹ • (x - p)‖ ^ 2 : ℝ) : EReal) ∧
      ∃ v ∈ subdiffPhi g h c xhat,
        ‖v‖ ≤ (3 * L * β * t + 2) * ‖t⁻¹ • (x - p)‖ := by sorry

end ErrBoundQG.ProxLin
