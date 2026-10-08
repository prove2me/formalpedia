-- Prove2me | Theorems.Thm_AdaGrad_Diag_primal_dual_gradient_term
-- name    : AdaGrad.Diag.primal_dual_gradient_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:31:14.120987+00:00
-- url     : https://prove2.me/theorems/a46748f5-eb65-43a9-855f-4ed43b6f480f
-- title:
--   §3, after (13) — with δ ≥ maxₜ‖gₜ‖∞, Σₜ‖gₜ‖²_{ψ*_{t−1}} ≤ 2 Σᵢ‖g_{1:T,i}‖₂
-- statement:
--   Let $g_1,g_2,\dots\in\mathbb R^d$ be any sequence, $s_{t,i}=\|g_{1:t,i}\|_2$ (with $s_{0,i}=0$), $T$ a horizon and $\delta\ge0$ with $\delta\ge\max_{1\le t\le T}\|g_t\|_\infty$. With AdaGrad's proximal functions $\psi_t(x)=\frac12\langle x,(\delta I+\mathrm{diag}(s_t))x\rangle$, whose squared dual norms are $\|g\|^2_{\psi_t^*}=\sum_ig_i^2/(\delta+s_{t,i})$,
--   $$\sum_{t=1}^T\|g_t\|^2_{\psi_{t-1}^*}\le2\sum_{i=1}^d\|g_{1:T,i}\|_2 .$$
--
--   This is the inequality (13) for the primal-dual subgradient update, whose regret bound (Proposition 2) measures round $t$'s subgradient in the dual norm of the previous round's proximal function.
--
--   **Formalization Note** The page states the per-round comparison with $\langle g_t,\mathrm{diag}(s_t)^{-1}g_t\rangle$ and says the same reasoning gives (13); the statement here is that summed conclusion. Division uses Lean's $0/0=0$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2131, §3, paragraph after (13)

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

namespace AdaGrad.Diag

/-- Duchi, Hazan, Singer, JMLR 12 (2011), §3, paragraph after (13), p. 2131: if
`δ ≥ max_{t ≤ T} ‖g_t‖∞`, then the squared dual norms for the *previous* round's proximal
function `ψ_{t−1}(x) = ½⟨x, (δI + diag(s_{t−1})) x⟩` (with `s_0 = 0`) satisfy the inequality (13):
`∑_{t=1}^T ‖g_t‖²_{ψ_{t−1}*} = ∑_{t=1}^T ∑_i g_{t,i}² / (δ + s_{t−1,i}) ≤ 2 ∑_{i=1}^d ‖g_{1:T,i}‖₂`. -/
theorem primal_dual_gradient_term {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (hδ : 0 ≤ δ) (T : ℕ) (hδg : ∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ) :
    ∑ t ∈ Finset.Icc 1 T, dualNormSq (adaWeights δ g (t - 1)) (g t) ≤ 2 * ∑ i, s g T i := by sorry

end AdaGrad.Diag
