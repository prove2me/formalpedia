-- Prove2me | Theorems.Thm_AdaGrad_Diag_lemma_4
-- name    : AdaGrad.Diag.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:31:21.589405+00:00
-- url     : https://prove2.me/theorems/efa28791-70e3-4020-8be0-d0aaa51fbd5f
-- title:
--   Lemma 4 — Σₜ⟨gₜ, diag(sₜ)⁻¹gₜ⟩ ≤ 2 Σᵢ‖g_{1:T,i}‖₂
-- statement:
--   Let $g_1,g_2,\dots\in\mathbb R^d$ be any sequence of (sub)gradients, and let $s_{t,i}=\|g_{1:t,i}\|_2=\big(\sum_{\tau=1}^tg_{\tau,i}^2\big)^{1/2}$ as in Algorithm 1. Then for every $T$,
--   $$\sum_{t=1}^T\big\langle g_t,\mathrm{diag}(s_t)^{-1}g_t\big\rangle\le2\sum_{i=1}^d\|g_{1:T,i}\|_2 .$$
--   Here $\langle g_t,\mathrm{diag}(s_t)^{-1}g_t\rangle=\sum_i g_{t,i}^2/s_{t,i}$, and $\mathrm{diag}(s_t)^{-1}$ is the pseudo-inverse: if $s_{t,i}=0$ then $g_{t,i}=0$ and the term is $0$.
--
--   The lemma is the source of the per-coordinate quantity $\sum_i\|g_{1:T,i}\|_2$ in AdaGrad's regret bound.
--
--   **Formalization Note** The pseudo-inverse is Lean's division with $0/0=0$. The lemma is stated for an arbitrary sequence $g$: it does not depend on how the subgradients were generated.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2131, Lemma 4 (proof p. 2149, Appendix C)

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

namespace AdaGrad.Diag

/-- Duchi, Hazan, Singer, JMLR 12 (2011), Lemma 4, p. 2131: for any sequence of (sub)gradients
`g_1, g_2, … ∈ ℝ^d` and `s_{t,i} = ‖g_{1:t,i}‖₂`,
`∑_{t=1}^T ⟨g_t, diag(s_t)⁻¹ g_t⟩ ≤ 2 ∑_{i=1}^d ‖g_{1:T,i}‖₂`.
`⟨g_t, diag(s_t)⁻¹ g_t⟩ = ∑_i g_{t,i}² / s_{t,i}` is `dualNormSq (s g t) (g t)`; `diag(s_t)⁻¹` is the
pseudo-inverse, i.e. `0/0 = 0` (if `s_{t,i} = 0` then `g_{t,i} = 0`). -/
theorem lemma_4 {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, dualNormSq (s g t) (g t) ≤ 2 * ∑ i, s g T i := by sorry

end AdaGrad.Diag
