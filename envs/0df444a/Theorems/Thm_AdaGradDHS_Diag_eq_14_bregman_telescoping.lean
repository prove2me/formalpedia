-- Prove2me | Theorems.Thm_AdaGradDHS_Diag_eq_14_bregman_telescoping
-- name    : AdaGradDHS.Diag.eq_14_bregman_telescoping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:21:05.712166+00:00
-- url     : https://prove2.me/theorems/205eb416-42cd-4c7d-9a59-77ae30aae78b
-- title:
--   Eq. (14): telescoping of the Bregman differences of diagonal AdaGrad
-- statement:
--   Let $\delta \in \mathbb{R}$, $g_1, g_2, \dots \in \mathbb{R}^d$, $s_{t,i} = \|g_{1:t,i}\|_2$, $\psi_t(x) = \tfrac12\sum_i (\delta + s_{t,i})x_i^2$, let $x_1, x_2, \dots \in \mathbb{R}^d$ and $x^* \in \mathbb{R}^d$, and let $T \ge 1$. Then
--   $$\sum_{t=1}^{T-1} \Big[B_{\psi_{t+1}}(x^*, x_{t+1}) - B_{\psi_t}(x^*, x_{t+1})\Big] \le \frac12 \sum_{t=1}^{T-1} \|x^* - x_{t+1}\|_\infty^2 \,\langle s_{t+1} - s_t, \mathbf 1\rangle$$
--   $$\le \frac12 \max_{t \le T} \|x^* - x_t\|_\infty^2 \sum_{i=1}^d \|g_{1:T,i}\|_2 - \frac12 \|x^* - x_1\|_\infty^2 \,\langle s_1, \mathbf 1\rangle .$$
--
--   This bounds the middle term of the composite mirror-descent bound (11) for AdaGrad; its negative last term cancels part of $B_{\psi_1}(x^*, x_1)$.
--
--   **Formalization Note** $\sum_{t=1}^{T-1}$ ranges over $t \in \{1, \dots, T-1\}$, $\langle v, \mathbf 1\rangle = \sum_i v_i$, and the maximum is over $t = 1, \dots, T$.
--
--   Differences from the source:
--   - generalization: x_t the iterates of Algorithm 1 with update (4) → an arbitrary sequence x of vectors; reason: the display uses nothing about how the iterates are generated
--   - reading: ψ_t(x) = ⟨x, H_t x⟩ (p. 2123, displays pp. 2131–2132) vs ψ_t(x) = ½⟨x, H_t x⟩ (Figure 1) → ψ_t = adagradPsi δ g t = ½ Σ_i (δ + s_{t,i}) x_i² (Figure 1); reason: Theorem 5 is about the sequence defined by Algorithm 1 (Figure 1); under this convention the ½ and 1/(2η) of the displays and of Theorem 5 are the paper's
--   - encoding: rounds t = 1, …, T with Σ_{t=1}^{T−1}, ⟨v, 1⟩, max_{t≤T} → 1 ≤ T, Finset.Ico 1 T, ∑ i, v i, maxSupDev x xstar T; reason: the paper's range of rounds; at T = 0 the printed sums and maximum are undefined
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §3, p. 2131, eq. (14)

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_bregman
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_adagradPsi
import Definitions.Def_AdaGradDHS_Diag_supNorm
import Definitions.Def_AdaGradDHS_Diag_maxSupDev

namespace AdaGradDHS.Diag

/-- **Eq. (14): telescoping of the Bregman differences of diagonal AdaGrad.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §3, p. 2131, eq. (14): "Since ‖st+1 − st‖1 = ⟨st+1 − st, 1⟩ and ⟨sT, 1⟩ = Σ_{i=1}^d
‖g1:T,i‖2, we have Σ_{t=1}^{T−1} Bψt+1(x∗, xt+1) − Bψt(x∗, xt+1) ≤ ½ Σ_{t=1}^{T−1} ‖x∗ − xt+1‖∞²
⟨st+1 − st, 1⟩ ≤ ½ max_{t≤T} ‖x∗ − xt‖∞² Σ_{i=1}^d ‖g1:T,i‖2 − ½‖x∗ − x1‖∞² ⟨s1, 1⟩."

For every `δ`, every sequence `g`, every sequence `x` in `ℝ^d`, every `x*` and every `T ≥ 1`,
with `ψ_t = adagradPsi δ g t` and `s_{t,i} = accNorm g t i`:
`Σ_{t=1}^{T−1} [B_{ψ_{t+1}}(x*, x_{t+1}) − B_{ψ_t}(x*, x_{t+1})]
  ≤ ½ Σ_{t=1}^{T−1} ‖x* − x_{t+1}‖∞² Σ_i (s_{t+1,i} − s_{t,i})
  ≤ ½ max_{1≤t≤T} ‖x* − x_t‖∞² Σ_i s_{T,i} − ½ ‖x* − x_1‖∞² Σ_i s_{1,i}`.

**Formalization Note.** `Σ_{t=1}^{T−1}` is `Finset.Ico 1 T`; `⟨v, 1⟩ = Σ_i v_i`; `max_{t≤T}` is
`maxSupDev`, over the rounds `t = 1, …, T`. `T ≥ 1` is the paper's range of rounds (at `T = 0`
the right-hand side need not be nonnegative). The iterates `x` are arbitrary: the display uses
nothing about how they are generated. -/
theorem eq_14_bregman_telescoping {d : ℕ} (δ : ℝ) (g x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d))
    {T : ℕ} (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Ico 1 T,
        (bregman (adagradPsi δ g (t + 1)) xstar (x (t + 1)) -
          bregman (adagradPsi δ g t) xstar (x (t + 1))) ≤
        1 / 2 * ∑ t ∈ Finset.Ico 1 T,
          supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) ∧
      1 / 2 * ∑ t ∈ Finset.Ico 1 T,
          supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) ≤
        1 / 2 * maxSupDev x xstar T ^ 2 * ∑ i, accNorm g T i -
          1 / 2 * supNorm (xstar - x 1) ^ 2 * ∑ i, accNorm g 1 i := by sorry

end AdaGradDHS.Diag
