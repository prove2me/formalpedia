-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_eq_13_dual_norm_sum
-- name    : AdaGradDHS.Diag.eq_13_dual_norm_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:18:58.838172+00:00
-- url     : https://prove2.me/theorems/dd7df41b-8a42-41ca-9033-2c45525cd966
-- title:
--   Eq. (13): $\sum_t \|g_t\|^2_{\psi_t^*} \le 2\sum_i \|g_{1:T,i}\|_2$
-- statement:
--   Let $\delta \ge 0$, $g_1, g_2, \dots \in \mathbb{R}^d$, and $s_{t,i} = \|g_{1:t,i}\|_2$. For the proximal function with matrix $H_t = \delta I + \operatorname{diag}(s_t)$, the squared dual norm is $\|g\|^2_{\psi_t^*} = \langle g, (\delta I + \operatorname{diag}(s_t))^{-1} g\rangle$, and for every $T$
--   $$\sum_{t=1}^T \sum_{i=1}^d \frac{g_{t,i}^2}{\delta + s_{t,i}} \le 2 \sum_{i=1}^d \|g_{1:T,i}\|_2 .$$
--
--   This bounds the gradient term $\tfrac{\eta}{2}\sum_t \|f'_t(x_t)\|^2_{\psi_t^*}$ of the composite mirror-descent bound (11) for AdaGrad.
--
--   **Formalization Note** A zero denominator forces $\delta = 0$ and $s_{t,i} = 0$, hence $g_{t,i} = 0$; Lean's $x/0 = 0$ then gives the right value.
--
--   Differences from the source:
--   - generalization: g_t = f′_t(x_t) from Algorithm 1 → an arbitrary sequence g of vectors; reason: the inequality never uses that g_t is a subgradient
--   - encoding: ‖f′_t(x_t)‖²_{ψ*_t} → ∑ i, (g t i) ^ 2 / (δ + accNorm g t i), the paper's own formula ⟨g, (δI + diag(s_t))^{-1} g⟩ (p. 2131); reason: the paper identifies the two on the same page; x / 0 = 0 meets only zero numerators
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §3, p. 2131, eq. (13) and the display before it

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_accNorm

namespace AdaGradDHS.Diag

/-- **Eq. (13): `Σ_{t=1}^T ‖f′_t(x_t)‖²_{ψ*_t} ≤ 2 Σ_{i=1}^d ‖g_{1:T,i}‖₂` for every `δ ≥ 0`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §3, p. 2131: "it is easy to see that the associated dual-norm is ‖g‖²ψ∗t = ⟨g, (δI +
diag(st))−1 g⟩. … Thus, for any δ ≥ 0, Lemma 4 implies Σ_{t=1}^T ‖f′t(xt)‖²ψ∗t ≤ 2 Σ_{i=1}^d
‖g1:T,i‖2. (13)"

For `δ ≥ 0`, every sequence `g` and every `T`, with `s_{t,i} = accNorm g t i`,
`Σ_{t=1}^T Σ_i g_{t,i}² / (δ + s_{t,i}) ≤ 2 Σ_i s_{T,i}`.

**Formalization Note.** `‖g_t‖²_{ψ*_t}` is written as the paper's own formula
`⟨g_t, (δI + diag(s_t))⁻¹ g_t⟩ = Σ_i g_{t,i}² / (δ + s_{t,i})`, with `x / 0 = 0`; a zero
denominator forces `δ = 0` and `s_{t,i} = 0`, hence `g_{t,i} = 0`. `g` is arbitrary. -/
theorem eq_13_dual_norm_sum {d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, ∑ i, (g t i) ^ 2 / (δ + accNorm g t i) ≤ 2 * ∑ i, accNorm g T i := by sorry

end AdaGradDHS.Diag
