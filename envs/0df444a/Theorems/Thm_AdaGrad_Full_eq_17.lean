-- Prove2me | Theorems.Thm_AdaGrad_Full_eq_17
-- name    : AdaGrad.Full.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:45:58.862219+00:00
-- url     : https://prove2.me/theorems/6ce06175-40f7-45a9-8e98-138eac672ae5
-- title:
--   Inequalities (17) — the adaptive dual norms sum to at most $2\operatorname{tr}(G_T^{1/2})$
-- statement:
--   Let $g_1,g_2,\dots\in\mathbb R^d$, $\delta\ge0$, $G_t=\sum_{\tau\le t}g_\tau g_\tau^\top$, $S_t=G_t^{1/2}$ (so $S_0=0$), and let $\|v\|_{\psi_t^*}^2=\langle v,(\delta I+S_t)^\dagger v\rangle$ be the squared dual (semi)norm of $\psi_t(x)=\tfrac12\langle x,(\delta I+S_t)x\rangle$. Then
--
--   1. (mirror descent) $$\sum_{t=1}^T\|g_t\|_{\psi_t^*}^2\le2\operatorname{tr}(G_T^{1/2});$$
--   2. (primal-dual subgradient) if moreover $\delta\ge\|g_t\|_2$ for $t=1,\dots,T$, then $$\sum_{t=1}^T\|g_t\|_{\psi_{t-1}^*}^2\le2\operatorname{tr}(G_T^{1/2}).$$
--
--   These bound the gradient terms of Propositions 3 and 2 for full-matrix ADAGRAD.
--
--   **Formalization Note** The page's dual norm $\langle x,(\delta I+S_t)^{-1}x\rangle$ is a seminorm when $\delta=0$; it is written with the pseudo-inverse, which is the inverse when $\delta>0$. The $\psi_0$ of the second sum uses $H_0=\delta I$ ($S_0=0$). The statement is for arbitrary sequences $g_t$ (the paper's $f_t'(x_t)$).
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2135, (17)

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

namespace AdaGrad.Full

/-- Inequalities (17) (p. 2135): with `‖v‖²_{ψ*_t} = ⟨v, (δI + S_t)† v⟩`,
`∑_{t=1}^T ‖g_t‖²_{ψ*_t} ≤ 2 tr(G_T^{1/2})` for every `δ ≥ 0` (mirror descent), and
`∑_{t=1}^T ‖g_t‖²_{ψ*_{t−1}} ≤ 2 tr(G_T^{1/2})` when `δ ≥ ‖g_t‖₂` for `t ≤ T` (primal-dual). -/
theorem eq_17 {d : ℕ} (δ : ℝ) (hδ : 0 ≤ δ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, dualNormSq (H δ g t) (g t) ≤ 2 * (S g T).trace ∧
      ((∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ δ) →
        ∑ t ∈ Finset.Icc 1 T, dualNormSq (H δ g (t - 1)) (g t) ≤ 2 * (S g T).trace) := by sorry

end AdaGrad.Full
