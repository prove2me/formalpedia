-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_psi_T_bound
-- name    : AdaGradDHS.Diag.psi_T_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:21:45.971667+00:00
-- url     : https://prove2.me/theorems/57f4c894-66c3-4f59-aeba-f528cc05fece
-- title:
--   Bound on $\psi_T(x^*)$ in the unhalved convention (p. 2132)
-- statement:
--   Let $\delta \in \mathbb{R}$, $g_1, g_2, \dots \in \mathbb{R}^d$, $s_{T,i} = \|g_{1:T,i}\|_2$ and $\psi_T(x) = \tfrac12\sum_i(\delta + s_{T,i})x_i^2$ (Figure 1). For every $x^* \in \mathbb{R}^d$,
--   $$2\,\psi_T(x^*) = \langle x^*, H_T x^*\rangle = \delta\|x^*\|_2^2 + \langle x^*, \operatorname{diag}(s_T)x^*\rangle \le \delta\|x^*\|_2^2 + \|x^*\|_\infty^2 \sum_{i=1}^d \|g_{1:T,i}\|_2 .$$
--
--   This bounds the term $\tfrac1\eta\psi_T(x^*)$ of the primal-dual bound (10) for AdaGrad.
--
--   **Formalization Note** The display on p. 2132 writes $\psi_T(x^*) = \delta\|x^*\|_2^2 + \dots$, using the unhalved $\psi_T(x) = \langle x, H_T x\rangle$ of p. 2123; Figure 1's $\psi_T$ is half of it. The statement makes the factor explicit: its first part is the identity, its second the display's inequality.
--
--   Differences from the source:
--   - reading: ψ_T(x∗) = δ‖x∗‖₂² + ⟨x∗, diag(s_T)x∗⟩ (the unhalved ψ_T of p. 2123) → 2 * adagradPsi δ g T xstar = δ‖x*‖² + ∑ i, accNorm g T i * x*_i² (Figure 1's ψ_T is half of it); reason: the display holds for the unhalved ψ_T; stated for Figure 1's ψ_T it would be off by a factor 2
--   - encoding: ‖x∗‖∞², ⟨x∗, diag(s_T)x∗⟩ → supNorm xstar ^ 2, ∑ i, accNorm g T i * (xstar i) ^ 2; reason: same quantities
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §3, p. 2132 (unnumbered display "We also have ψT(x∗) = …")

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_adagradPsi
import Definitions.Def_AdaGradDHS_Diag_supNorm

namespace AdaGradDHS.Diag

/-- **Bound on `ψ_T(x*)` (in the unhalved convention `⟨x, H_T x⟩ = 2 ψ_T(x)`).**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §3, p. 2132 (unnumbered display): "We also have ψT(x∗) = δ‖x∗‖2² + ⟨x∗, diag(sT)x∗⟩ ≤
δ‖x∗‖2² + ‖x∗‖∞² Σ_{i=1}^d ‖g1:T,i‖2."

For every `δ`, every sequence `g`, every `T` and every `x*`, with `ψ_T = adagradPsi δ g T`
(Figure 1's `½⟨x, H_T x⟩`) and `s_{T,i} = accNorm g T i`:
`2 ψ_T(x*) = δ‖x*‖₂² + Σ_i s_{T,i} x*_i²` and
`δ‖x*‖₂² + Σ_i s_{T,i} x*_i² ≤ δ‖x*‖₂² + ‖x*‖∞² Σ_i s_{T,i}`.

**Formalization Note.** The display's `ψ_T` is the unhalved `⟨x, H_T x⟩` of p. 2123, which is
twice Figure 1's `ψ_T` (`adagradPsi`); the first conjunct records this, the second is the display's
inequality. `‖·‖` on `EuclideanSpace` is the ℓ2 norm. -/
theorem psi_T_bound {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) (xstar : EuclideanSpace ℝ (Fin d)) :
    2 * adagradPsi δ g T xstar = δ * ‖xstar‖ ^ 2 + ∑ i, accNorm g T i * (xstar i) ^ 2 ∧
      δ * ‖xstar‖ ^ 2 + ∑ i, accNorm g T i * (xstar i) ^ 2 ≤
        δ * ‖xstar‖ ^ 2 + supNorm xstar ^ 2 * ∑ i, accNorm g T i := by sorry

end AdaGradDHS.Diag
