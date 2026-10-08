-- Prove2me | Theorems.Thm_AdaGrad_Full_display_bregman_increment
-- name    : AdaGrad.Full.display_bregman_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:45:22.522366+00:00
-- url     : https://prove2.me/theorems/f54fa470-d215-4583-9900-8a99b6dcfbc6
-- title:
--   §4, proof of Theorem 7 — the increment of the Bregman divergences is at most ½‖x*−y‖₂² tr(G_{t+1}^{1/2}−G_t^{1/2})
-- statement:
--   Let $g_1,g_2,\dots\in\mathbb R^d$, $G_t=\sum_{\tau\le t}g_\tau g_\tau^\top$, $\delta\in\mathbb R$, $H_t=\delta I+G_t^{1/2}$ and $B_{\psi_t}(x,y)=\tfrac12\langle x-y,H_t(x-y)\rangle$. For every $t\ge0$ and all $x^*,y\in\mathbb R^d$,
--   $$B_{\psi_{t+1}}(x^*,y)-B_{\psi_t}(x^*,y)=\tfrac12\big\langle x^*-y,(G_{t+1}^{1/2}-G_t^{1/2})(x^*-y)\big\rangle\le\tfrac12\|x^*-y\|_2^2\operatorname{tr}\big(G_{t+1}^{1/2}-G_t^{1/2}\big).$$
--
--   Applied with $y=x_{t+1}$ it bounds the middle sum of Proposition 3 for full-matrix ADAGRAD.
--
--   **Formalization Note** The page passes through $\tfrac12\|x^*-y\|_2^2\lambda_{\max}(G_{t+1}^{1/2}-G_t^{1/2})$; that intermediate quantity is not stated, only the equality and the outer inequality.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2134, §4, proof of Theorem 7, first display

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

namespace AdaGrad.Full

/-- §4, proof of Theorem 7, first display (p. 2134): for ADAGRAD's proximal matrices
`H_t = δI + G_t^{1/2}`, `B_{ψ_{t+1}}(x*, y) − B_{ψ_t}(x*, y) = ½⟨x* − y, (G_{t+1}^{1/2} − G_t^{1/2})(x* − y)⟩`
and this is at most `½‖x* − y‖₂² tr(G_{t+1}^{1/2} − G_t^{1/2})`. -/
theorem display_bregman_increment {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (xstar y : EuclideanSpace ℝ (Fin d)) :
    bregman (H δ g (t + 1)) xstar y - bregman (H δ g t) xstar y
        = 1 / 2 * mInner (S g (t + 1) - S g t) (xstar - y) (xstar - y) ∧
      1 / 2 * mInner (S g (t + 1) - S g t) (xstar - y) (xstar - y)
        ≤ 1 / 2 * ‖xstar - y‖ ^ 2 * (S g (t + 1) - S g t).trace := by sorry

end AdaGrad.Full
