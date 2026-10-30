-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_bregman_one_bound
-- name    : AdaGradDHS.Diag.bregman_one_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:22:18.87054+00:00
-- url     : https://prove2.me/theorems/d2a29ef7-706c-4e89-820f-83ef684a0a81
-- title:
--   Bound on $B_{\psi_1}(x^*, x_1)$ (corrected: $\tfrac\delta2\|x^*-x_1\|_2^2$ added)
-- statement:
--   Let $\delta \in \mathbb{R}$, $g_1, g_2, \dots \in \mathbb{R}^d$, $s_{1,i} = |g_{1,i}|$ and $\psi_1(x) = \tfrac12\sum_i(\delta + s_{1,i})x_i^2$ (Figure 1). For all $x^*, x_1 \in \mathbb{R}^d$,
--   $$B_{\psi_1}(x^*, x_1) \le \frac\delta2 \|x^* - x_1\|_2^2 + \frac12 \|x^* - x_1\|_\infty^2 \,\langle \mathbf 1, s_1\rangle .$$
--
--   This bounds the first term $\tfrac1\eta B_{\psi_1}(x^*, x_1)$ of the composite mirror-descent bound (11) for AdaGrad; together with (14) it gives the mirror-descent clause of Theorem 5.
--
--   **Formalization Note** The fact used on p. 2132, $B_{\psi_1}(x^*, x_1) \le \tfrac12\|x^* - x_1\|_\infty^2\langle 1, s_1\rangle$, omits the $\delta$-part of $\psi_1$ and is false for $\delta > 0$. Since $B_{\psi_1}(x^*, x_1) = \tfrac12\sum_i(\delta + s_{1,i})(x^*_i - x_{1,i})^2$, the corrected bound adds exactly $\tfrac\delta2\|x^* - x_1\|_2^2$; at $\delta = 0$ it is the printed fact.
--
--   Differences from the source:
--   - correction: B_{ψ_1}(x∗, x_1) ≤ ½‖x∗ − x_1‖∞² ⟨1, s_1⟩ → B_{ψ_1}(x*, x_1) ≤ δ/2 ‖x* − x_1‖₂² + ½ ‖x* − x_1‖∞² ∑_i s_{1,i}; reason: the printed fact is false for δ > 0: d = 1, δ = 1, g_1 = 0, x_1 = 0, x* = 1 give B_{ψ_1}(x*, x_1) = ½ > 0; the added term is the δ-part of ψ_1, zero at δ = 0
--   - generalization: x_1, g_1 of Algorithm 1 → any x_1 ∈ ℝ^d and any sequence g; reason: the bound is algebraic in x_1 and g_1
--   - reading: ψ_t(x) = ⟨x, H_t x⟩ (p. 2123, displays pp. 2131–2132) vs ψ_t(x) = ½⟨x, H_t x⟩ (Figure 1) → ψ_t = adagradPsi δ g t = ½ Σ_i (δ + s_{t,i}) x_i² (Figure 1); reason: Theorem 5 is about the sequence defined by Algorithm 1 (Figure 1); under this convention the ½ and 1/(2η) of the displays and of Theorem 5 are the paper's
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §3, p. 2132 (unnumbered, "the fact that Bψ1(x∗, x1) ≤ ½‖x∗ − x1‖∞² ⟨1, s1⟩")

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_bregman
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_adagradPsi
import Definitions.Def_AdaGradDHS_Diag_supNorm

namespace AdaGradDHS.Diag

/-- **Bound on `B_{ψ_1}(x*, x_1)` (corrected: the term `(δ/2)‖x* − x_1‖₂²` is added).**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §3, p. 2132 (unnumbered): "Combining the above arguments with Corollaries 2 and 3, and
using (14) with the fact that Bψ1(x∗, x1) ≤ ½‖x∗ − x1‖∞² ⟨1, s1⟩, we have proved the following
theorem."

For every `δ`, every sequence `g` and all `x*, x_1 ∈ ℝ^d`, with `ψ_1 = adagradPsi δ g 1` and
`s_{1,i} = accNorm g 1 i`:
`B_{ψ_1}(x*, x_1) ≤ (δ/2)‖x* − x_1‖₂² + ½ ‖x* − x_1‖∞² Σ_i s_{1,i}`.

**Formalization Note.** The printed "fact" omits the `δ`-part of `ψ_1` and is false for `δ > 0`:
`d = 1`, `δ = 1`, `g_1 = 0`, `x_1 = 0`, `x* = 1` give `B_{ψ_1}(x*, x_1) = ½ > 0`. Adding
`(δ/2)‖x* − x_1‖₂²` (`B_{ψ_1}(x*, x_1) = ½ Σ_i (δ + s_{1,i})(x*_i − x_{1,i})²` exactly) restores it;
at `δ = 0` it is the printed fact. `⟨1, s_1⟩ = Σ_i s_{1,i}`. -/
theorem bregman_one_bound {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (xstar x1 : EuclideanSpace ℝ (Fin d)) :
    bregman (adagradPsi δ g 1) xstar x1 ≤
      δ / 2 * ‖xstar - x1‖ ^ 2 + 1 / 2 * supNorm (xstar - x1) ^ 2 * ∑ i, accNorm g 1 i := by sorry

end AdaGradDHS.Diag
