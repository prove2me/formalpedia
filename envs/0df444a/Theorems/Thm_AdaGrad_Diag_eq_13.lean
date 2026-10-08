-- Prove2me | Theorems.Thm_AdaGrad_Diag_eq_13
-- name    : AdaGrad.Diag.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:31:23.814564+00:00
-- url     : https://prove2.me/theorems/3129f434-d384-4ea7-a39f-1a57f31b83c5
-- title:
--   (13) — Σₜ‖gₜ‖²_{ψₜ*} ≤ 2 Σᵢ‖g_{1:T,i}‖₂ for every δ ≥ 0
-- statement:
--   Let $g_1,g_2,\dots\in\mathbb R^d$ be any sequence, $s_{t,i}=\|g_{1:t,i}\|_2$, and $\delta\ge0$. For AdaGrad's proximal functions $\psi_t(x)=\frac12\langle x,(\delta I+\mathrm{diag}(s_t))x\rangle$ the squared dual norm is $\|g\|^2_{\psi_t^*}=\sum_ig_i^2/(\delta+s_{t,i})$, and for every $T$
--   $$\sum_{t=1}^T\|g_t\|^2_{\psi_t^*}\le2\sum_{i=1}^d\|g_{1:T,i}\|_2 .$$
--
--   This bounds the gradient term of the composite mirror descent regret bound (Proposition 3) for diagonal AdaGrad.
--
--   **Formalization Note** The dual norm uses Lean's division with $0/0=0$; a zero weight $\delta+s_{t,i}=0$ occurs only when $\delta=0$ and $s_{t,i}=0$, in which case $g_{t,i}=0$, matching the paper's remark that "if $s_{t,i}=0$ then $g_{t,i}=0$".
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2131, §3, (13)

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

namespace AdaGrad.Diag

/-- Duchi, Hazan, Singer, JMLR 12 (2011), §3, inequality (13), p. 2131: for any `δ ≥ 0`, the
squared dual norms of the subgradients for AdaGrad's proximal functions
`ψ_t(x) = ½⟨x, (δI + diag(s_t)) x⟩` satisfy
`∑_{t=1}^T ‖g_t‖²_{ψ_t*} = ∑_{t=1}^T ∑_i g_{t,i}² / (δ + s_{t,i}) ≤ 2 ∑_{i=1}^d ‖g_{1:T,i}‖₂`. -/
theorem eq_13 {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (δ : ℝ) (hδ : 0 ≤ δ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, dualNormSq (adaWeights δ g t) (g t) ≤ 2 * ∑ i, s g T i := by sorry

end AdaGrad.Diag
