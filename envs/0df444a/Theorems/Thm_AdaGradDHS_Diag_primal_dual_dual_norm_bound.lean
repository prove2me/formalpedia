-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_primal_dual_dual_norm_bound
-- name    : AdaGradDHS.Diag.primal_dual_dual_norm_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:19:28.935451+00:00
-- url     : https://prove2.me/theorems/677abfde-a1ae-4b3b-918c-903de58566d2
-- title:
--   Dual-norm bound for the primal-dual update when $\delta \ge \max_t\|g_t\|_\infty$ (p. 2131)
-- statement:
--   Let $\delta \ge 0$, $g_1, g_2, \dots \in \mathbb{R}^d$, $T \in \mathbb{N}$, and assume $\|g_t\|_\infty \le \delta$ for $t = 1, \dots, T$. With $s_{t,i} = \|g_{1:t,i}\|_2$ (so $s_0 = 0$) and $\|g\|^2_{\psi_{t-1}^*} = \sum_i g_i^2/(\delta + s_{t-1,i})$:
--
--   1. for every $t \in \{1, \dots, T\}$,
--   $$\|g_t\|^2_{\psi_{t-1}^*} = \sum_{i=1}^d \frac{g_{t,i}^2}{\delta + s_{t-1,i}} \le \sum_{i=1}^d \frac{g_{t,i}^2}{s_{t,i}} = \langle g_t, \operatorname{diag}(s_t)^{-1} g_t\rangle ;$$
--   2. consequently, the analogue of (13) for $\psi_{t-1}^*$ holds:
--   $$\sum_{t=1}^T \sum_{i=1}^d \frac{g_{t,i}^2}{\delta + s_{t-1,i}} \le 2 \sum_{i=1}^d \|g_{1:T,i}\|_2 .$$
--
--   The primal-dual bound (10) measures the gradient $g_t$ in the dual norm of the previous proximal function $\psi_{t-1}$; the condition on $\delta$ makes this one-step lag harmless.
--
--   **Formalization Note** $t - 1$ is used only for $t \ge 1$. Divisions by zero follow $x/0 = 0$ and meet only zero numerators under the hypotheses.
--
--   Differences from the source:
--   - generalization: g_t = f′_t(x_t) from Algorithm 1 → an arbitrary sequence g of vectors; reason: the bound never uses that g_t is a subgradient
--   - encoding: ‖g_t‖²_{ψ*_{t−1}} and δ ≥ max_t ‖g_t‖∞ → ∑ i, (g t i) ^ 2 / (δ + accNorm g (t - 1) i) and ∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ; reason: the paper's dual-norm formula (p. 2131) at s_{t−1}; the maximum over the rounds is the conjunction over t
--   - reading: "we follow the same lines of reasoning to achieve the inequality (13)" → the second conjunct: ∑_t ‖g_t‖²_{ψ*_{t−1}} ≤ 2 ∑_i ‖g_{1:T,i}‖₂; reason: the sentence asserts (13) with ψ*_{t−1} in place of ψ*_t; both conjuncts are stated
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §3, p. 2131 (unnumbered, the sentence after (13))

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_supNorm

namespace AdaGradDHS.Diag

/-- **Dual-norm bound for the primal-dual update: `‖g_t‖²_{ψ*_{t−1}} ≤ ⟨g_t, diag(s_t)⁻¹ g_t⟩`
when `δ ≥ max_t ‖g_t‖∞`, and the inequality (13) for `ψ*_{t−1}`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §3, p. 2131 (unnumbered, the sentence after (13)): "To obtain a bound for a primal-dual
subgradient method, we set δ ≥ maxt ‖gt‖∞, in which case ‖gt‖²ψ∗t−1 ≤ ⟨gt, diag(st)−1 gt⟩, and we
follow the same lines of reasoning to achieve the inequality (13)."

For `δ ≥ 0`, every sequence `g` and every `T` with `‖g_t‖∞ ≤ δ` for `t = 1, …, T`, writing
`s_{t,i} = accNorm g t i`:
1. for every `t ∈ {1, …, T}`, `Σ_i g_{t,i}² / (δ + s_{t−1,i}) ≤ Σ_i g_{t,i}² / s_{t,i}`;
2. `Σ_{t=1}^T Σ_i g_{t,i}² / (δ + s_{t−1,i}) ≤ 2 Σ_i s_{T,i}`.

**Formalization Note.** `‖g‖²_{ψ*_{t−1}} = ⟨g, (δI + diag(s_{t−1}))⁻¹ g⟩` (p. 2131) is written as
`Σ_i g_i² / (δ + s_{t−1,i})`; `t − 1` is natural subtraction, used only for `t ≥ 1`; at `t = 1`,
`s_0 = 0`. Divisions by zero follow `x / 0 = 0` and meet only zero numerators under the
hypotheses. -/
theorem primal_dual_dual_norm_bound {d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ)
    (hgδ : ∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ) :
    (∀ t ∈ Finset.Icc 1 T,
        ∑ i, (g t i) ^ 2 / (δ + accNorm g (t - 1) i) ≤ ∑ i, (g t i) ^ 2 / accNorm g t i) ∧
      ∑ t ∈ Finset.Icc 1 T, ∑ i, (g t i) ^ 2 / (δ + accNorm g (t - 1) i) ≤
        2 * ∑ i, accNorm g T i := by sorry

end AdaGradDHS.Diag
