-- Prove2me | Theorems.Thm_AdaGrad_Diag_eq_14
-- name    : AdaGrad.Diag.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:31:28.224539+00:00
-- url     : https://prove2.me/theorems/f55d88ec-6fd1-47b9-9fc4-94f66cb5ffe1
-- title:
--   (14) — the Bregman drift of diagonal AdaGrad is at most ½ maxₜ‖x* − xₜ‖∞² Σᵢ‖g_{1:T,i}‖₂ − ½‖x* − x₁‖∞²⟨s₁, 1⟩
-- statement:
--   Let $g_1,g_2,\dots\in\mathbb R^d$ and $x_1,x_2,\dots,x^*\in\mathbb R^d$ be arbitrary, $\delta\in\mathbb R$, $s_{t,i}=\|g_{1:t,i}\|_2$, and $B_{\psi_t}(y,z)=\frac12\sum_i(\delta+s_{t,i})(y_i-z_i)^2$ the Bregman divergence of AdaGrad's $\psi_t(x)=\frac12\langle x,(\delta I+\mathrm{diag}(s_t))x\rangle$. For every $T\ge1$,
--   $$\sum_{t=1}^{T-1}\big[B_{\psi_{t+1}}(x^*,x_{t+1})-B_{\psi_t}(x^*,x_{t+1})\big]\le\frac12\sum_{t=1}^{T-1}\|x^*-x_{t+1}\|_\infty^2\langle s_{t+1}-s_t,\mathbf 1\rangle$$
--   $$\le\frac12\max_{1\le t\le T}\|x^*-x_t\|_\infty^2\sum_{i=1}^d\|g_{1:T,i}\|_2-\frac12\|x^*-x_1\|_\infty^2\langle s_1,\mathbf 1\rangle .$$
--
--   This bounds the Bregman-divergence drift term of the composite mirror descent regret bound (Proposition 3) for diagonal AdaGrad.
--
--   **Formalization Note** Both inequalities are stated, as a conjunction. $\delta$ cancels from the left-hand side and is arbitrary. The maximum is over $t\in\{1,\dots,T\}$ (`Finset.sup'`, well defined because $T\ge1$). $\langle s_{t+1}-s_t,\mathbf 1\rangle=\sum_i(s_{t+1,i}-s_{t,i})$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2131, §3, (14)

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

namespace AdaGrad.Diag

/-- Duchi, Hazan, Singer, JMLR 12 (2011), §3, inequality (14), p. 2131: for AdaGrad's diagonal
proximal functions `ψ_t(x) = ½⟨x, (δI + diag(s_t)) x⟩`, any points `x_1, x_2, … , x* ∈ ℝ^d`,
any subgradients `g_t` and any `T ≥ 1`,
`∑_{t=1}^{T−1} [B_{ψ_{t+1}}(x*, x_{t+1}) − B_{ψ_t}(x*, x_{t+1})]
   ≤ ½ ∑_{t=1}^{T−1} ‖x* − x_{t+1}‖∞² ⟨s_{t+1} − s_t, 1⟩
   ≤ ½ max_{t≤T} ‖x* − x_t‖∞² ∑_{i=1}^d ‖g_{1:T,i}‖₂ − ½ ‖x* − x_1‖∞² ⟨s_1, 1⟩`.
The maximum is over `t ∈ {1, …, T}`. -/
theorem eq_14 {d : ℕ} (δ : ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d))
    (xstar : EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Ico 1 T,
        (bregman (adaWeights δ g (t + 1)) xstar (x (t + 1))
          - bregman (adaWeights δ g t) xstar (x (t + 1)))
      ≤ (1 / 2) * ∑ t ∈ Finset.Ico 1 T,
          supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (s g (t + 1) i - s g t i) ∧
    (1 / 2) * ∑ t ∈ Finset.Ico 1 T,
          supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (s g (t + 1) i - s g t i)
      ≤ (1 / 2) * (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
            (fun t => supNorm (xstar - x t) ^ 2) * ∑ i, s g T i
        - (1 / 2) * supNorm (xstar - x 1) ^ 2 * ∑ i, s g 1 i := by sorry

end AdaGrad.Diag
