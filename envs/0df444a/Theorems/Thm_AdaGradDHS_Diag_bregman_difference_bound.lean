-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_bregman_difference_bound
-- name    : AdaGradDHS.Diag.bregman_difference_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:20:16.469144+00:00
-- url     : https://prove2.me/theorems/f06b20c8-bf8d-4f64-a4f7-d8c1ddd1b984
-- title:
--   Difference of consecutive Bregman divergences of diagonal AdaGrad (p. 2131)
-- statement:
--   Let $\delta \in \mathbb{R}$, $g_1, g_2, \dots \in \mathbb{R}^d$, $s_{t,i} = \|g_{1:t,i}\|_2$ and $\psi_t(x) = \tfrac12\sum_i (\delta + s_{t,i})x_i^2$. For every $t$ and all $x^*, y \in \mathbb{R}^d$,
--   $$B_{\psi_{t+1}}(x^*, y) - B_{\psi_t}(x^*, y) = \tfrac12 \big\langle x^* - y, \operatorname{diag}(s_{t+1} - s_t)(x^* - y)\big\rangle \le \tfrac12 \|x^* - y\|_\infty^2 \, \|s_{t+1} - s_t\|_1 .$$
--
--   In the paper $y = x_{t+1}$; summing these differences over $t$ gives (14), which controls the middle term of the mirror-descent bound (11).
--
--   **Formalization Note** The quadratic form is written $\sum_i (s_{t+1,i} - s_{t,i})(x^*_i - y_i)^2$ and $\|s_{t+1} - s_t\|_1$ as $\sum_i |s_{t+1,i} - s_{t,i}|$; $\max_i (x^*_i - y_i)^2 = \|x^* - y\|_\infty^2$.
--
--   Differences from the source:
--   - generalization: evaluated at y = x_{t+1} → any y ∈ ℝ^d; reason: the identity and the bound are algebraic in y
--   - reading: ψ_t(x) = ⟨x, H_t x⟩ (p. 2123, displays pp. 2131–2132) vs ψ_t(x) = ½⟨x, H_t x⟩ (Figure 1) → ψ_t = adagradPsi δ g t = ½ Σ_i (δ + s_{t,i}) x_i² (Figure 1); reason: Theorem 5 is about the sequence defined by Algorithm 1 (Figure 1); under this convention the ½ and 1/(2η) of the displays and of Theorem 5 are the paper's
--   - encoding: ½⟨x∗ − y, diag(s_{t+1} − s_t)(x∗ − y)⟩, max_i (x∗_i − y_i)², ‖s_{t+1} − s_t‖₁ → 1/2 * ∑ i, (accNorm g (t+1) i − accNorm g t i) * (xstar i − y i)^2, supNorm (xstar − y)^2, ∑ i, |accNorm g (t+1) i − accNorm g t i|; reason: same quantities
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §3, p. 2131 (unnumbered display before (14))

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_bregman
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_adagradPsi
import Definitions.Def_AdaGradDHS_Diag_supNorm

namespace AdaGradDHS.Diag

/-- **Difference of consecutive Bregman divergences of diagonal AdaGrad.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §3, p. 2131 (unnumbered display): "Bψt+1(x∗, xt+1) − Bψt(x∗, xt+1) = ½⟨x∗ − xt+1,
diag(st+1 − st)(x∗ − xt+1)⟩ ≤ ½ maxi (x∗i − xt+1,i)² ‖st+1 − st‖1."

For every `δ`, every sequence `g`, every `t` and all `x*, y ∈ ℝ^d`, with `ψ_t = adagradPsi δ g t`
and `s_{t,i} = accNorm g t i`:
`B_{ψ_{t+1}}(x*, y) − B_{ψ_t}(x*, y) = ½ Σ_i (s_{t+1,i} − s_{t,i})(x*_i − y_i)²`
and this is at most `½ ‖x* − y‖∞² Σ_i |s_{t+1,i} − s_{t,i}|`.

**Formalization Note.** The paper evaluates at `y = x_{t+1}`; the identity and the bound hold for
every `y`. `ψ_t` is Figure 1's `½⟨x, H_t x⟩`, under which the display holds as printed.
`‖s_{t+1} − s_t‖₁` is `Σ_i |s_{t+1,i} − s_{t,i}|` and `max_i (x*_i − y_i)²` is `‖x* − y‖∞²`. -/
theorem bregman_difference_bound {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (xstar y : EuclideanSpace ℝ (Fin d)) :
    bregman (adagradPsi δ g (t + 1)) xstar y - bregman (adagradPsi δ g t) xstar y =
        1 / 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) * (xstar i - y i) ^ 2 ∧
      1 / 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) * (xstar i - y i) ^ 2 ≤
        1 / 2 * supNorm (xstar - y) ^ 2 * ∑ i, |accNorm g (t + 1) i - accNorm g t i| := by sorry

end AdaGradDHS.Diag
