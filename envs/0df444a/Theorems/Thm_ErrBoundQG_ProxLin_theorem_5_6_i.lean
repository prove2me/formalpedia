-- Prove2me | Theorems.Thm_ErrBoundQG_ProxLin_theorem_5_6_i
-- name    : ErrBoundQG.ProxLin.theorem_5_6_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:19.924234+00:00
-- url     : https://prove2.me/theorems/fdf9de0d-30b6-4296-b5f1-2763bcaca708
-- title:
--   Theorem 5.6, (5.7), p. 18 — the prox-gradient norm is bounded by stationarity residual
-- statement:
--   For the convex-composite problem $\varphi=g+h\circ c$, any $x$, $t>0$, and prox-linear point $x^t$ satisfy
--
--   $$
--   \frac12\|\mathcal G_t(x)\|\le\operatorname{dist}(0,\partial\varphi(x)).
--   $$
--
--   This compares the step length with the first-order stationarity residual at the same point.
--
--   **Formalization Note** The right-hand distance is $+\infty$ when the subdifferential is empty. The Lean statement equivalently bounds $\|\mathcal G_t(x)\|/2$ by the norm of every subgradient.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 18, Theorem 5.6, (5.7)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

namespace ErrBoundQG.ProxLin

theorem theorem_5_6_i {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (t : ℝ) (ht : 0 < t) (x p : En n)
    (hp : IsProxLinPoint g h c t x p) :
    ∀ v ∈ subdiffPhi g h c x,
      (1 / 2 : ℝ) * ‖t⁻¹ • (x - p)‖ ≤ ‖v‖ := by sorry

end ErrBoundQG.ProxLin
