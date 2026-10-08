-- Prove2me | Theorems.Thm_ErrBoundQG_ProxLin_prox_grad_eq_zero_iff
-- name    : ErrBoundQG.ProxLin.prox_grad_eq_zero_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:40.101924+00:00
-- url     : https://prove2.me/theorems/fcc94192-bb5a-44a7-b3ad-4a36bbaf5d26
-- title:
--   §5, p. 14 — a zero prox-gradient is equivalent to stationarity
-- statement:
--   In the convex-composite problem $\varphi=g+h\circ c$, let $t>0$ and let $x^t$ minimize the prox-linear subproblem at $x$. Then
--
--   $$
--   t^{-1}(x-x^t)=0\quad\Longleftrightarrow\quad 0\in\partial\varphi(x).
--   $$
--
--   Thus the fixed points of the prox-linear step are precisely the stationary points defined by the paper's composite subdifferential.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 14, §5 after (5.2)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

namespace ErrBoundQG.ProxLin

theorem prox_grad_eq_zero_iff {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (t : ℝ) (ht : 0 < t) (x p : En n)
    (hp : IsProxLinPoint g h c t x p) :
    t⁻¹ • (x - p) = 0 ↔ IsStationary g h c x := by sorry

end ErrBoundQG.ProxLin
