-- Prove2me | Theorems.Thm_DecBilevel_SLDBO_lemma_A_11
-- name    : DecBilevel.SLDBO.lemma_A_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:36.798536+00:00
-- url     : https://prove2.me/theorems/546fcc5a-637e-45a7-bbf0-1ee570fabe46
-- title:
--   Lemma A.11, (53), p. 22 — y* is (L_{f,1}/σ)-Lipschitz and v* is (L_v/σ)-Lipschitz
-- statement:
--   Let $F_i,f_i$ ($n\ge1$) satisfy Assumption 2.1, let $y^*(x)$ minimize $f(x,\cdot)$ for every $x$, and let $v^*(x)=[\nabla^2_{22}f(x,y^*(x))]^{-1}\nabla_2F(x,y^*(x))$. With $L_v=(L_{F,1}+L_{f,2}r_v)(1+L_{f,1}/\sigma)$ from (8), for all $x,x'\in\mathbb R^p$
--   $$\|y^*(x)-y^*(x')\|\le\frac{L_{f,1}}\sigma\|x-x'\|\qquad\text{and}\qquad\|v^*(x)-v^*(x')\|\le\frac{L_v}\sigma\|x-x'\|.$$
--
--   The page states (53) at $x=\bar x^{k+1}$, $x'=\bar x^k$; this is the same claim for all pairs, as the proof (54) establishes it.
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, p. 22, Lemma A.11, (53)–(54)

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO

theorem lemma_A_11 {n p q : ℕ} (hn : 0 < n) (F f : Fin n → E p → E q → ℝ)
    (σ LF0 LF1 Lf1 Lf2 : ℝ) (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2)
    (ystar : E p → E q) (hystar : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x)) (x x' : E p) :
    ‖ystar x - ystar x'‖ ≤ Lf1 / σ * ‖x - x'‖ ∧
    ‖vstar F f ystar x - vstar F f ystar x'‖ ≤ Lv σ LF0 LF1 Lf1 Lf2 / σ * ‖x - x'‖ := by sorry

end DecBilevel.SLDBO
