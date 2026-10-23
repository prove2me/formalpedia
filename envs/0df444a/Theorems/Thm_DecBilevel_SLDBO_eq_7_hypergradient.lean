-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_eq_7_hypergradient
-- name    : DecBilevel.SLDBO.eq_7_hypergradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:37.611991+00:00
-- url     : https://prove2.me/theorems/26c5a47f-1437-4574-918c-a183a1ca2d82
-- title:
--   (7), p. 3 — the hypergradient formula is the gradient of Φ
-- statement:
--   Let $F_i,f_i$ ($i=1,\dots,n$, $n\ge1$) satisfy Assumption 2.1, let $f=\frac1n\sum_if_i$, and let $y^*(x)$ minimize $f(x,\cdot)$ for every $x\in\mathbb R^p$. Then $\Phi(x)=\frac1n\sum_iF_i(x,y^*(x))$ is differentiable at every $x$, and its gradient is given by (7):
--   $$\nabla\Phi(x)=\frac1n\sum_{i=1}^n\nabla_1F_i(x,y^*(x))-\Big[\frac1n\sum_{i=1}^n\nabla^2_{12}f_i(x,y^*(x))\Big]\Big[\frac1n\sum_{i=1}^n\nabla^2_{22}f_i(x,y^*(x))\Big]^{-1}\frac1n\sum_{i=1}^n\nabla_2F_i(x,y^*(x)).$$
--
--   This identifies the quantity that Algorithm 1 tracks, and that Theorem 3.1 drives to zero, with the true gradient of the bilevel objective.
--
--   **Formalization Note.** The right-hand side is the definition `hypergrad`; the conclusion is `HasGradientAt Φ (hypergrad x) x`. Strong convexity makes $y^*(x)$ unique, so taking $y^*$ as a given minimizer map loses nothing.
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 3, (7)

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem eq_7_hypergradient {n p q : ℕ} (hn : 0 < n) (F f : Fin n → E p → E q → ℝ)
    (σ LF0 LF1 Lf1 Lf2 : ℝ) (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2)
    (ystar : E p → E q) (hystar : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x)) (x : E p) :
    HasGradientAt (Phi F ystar) (hypergrad F f ystar x) x := by sorry

end DecBilevel.SLDBO
