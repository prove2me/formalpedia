-- Prove2me | Theorems.Thm_ALADIN_DualDecomp_slack_elimination
-- name    : ALADIN.DualDecomp.slack_elimination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:04.507987+00:00
-- url     : https://prove2.me/theorems/8f7d1f88-76de-452a-9094-6bd15a19ef0a
-- title:
--   App. A, proof of Lemma 5 — eliminating the slack: min over s of (μ/2)‖s‖² − (λ_QP − λ)ᵀs = −‖λ_QP − λ‖²/(2μ)
-- statement:
--   Let $\mu > 0$ and $\lambda, \lambda_{\mathrm{QP}}\in\mathbb R^m$. Then for every $s\in\mathbb R^m$,
--   $$\frac{\mu}{2}\|s\|_2^2 - (\lambda_{\mathrm{QP}}-\lambda)^\top s\ \ge\ -\frac{1}{2\mu}\|\lambda_{\mathrm{QP}}-\lambda\|_2^2,$$
--   and equality holds if and only if $s = \frac1\mu(\lambda_{\mathrm{QP}}-\lambda)$.
--
--   In the proof of Lemma 5 this is the step that removes the slack variable $s$ from the dual of the coupled QP (3.3): the inner minimum over $s$ of $\frac\mu2\|s\|_2^2 - (\lambda_{\mathrm{QP}}-\lambda)^\top s$ equals $-\frac{1}{2\mu}\|\lambda_{\mathrm{QP}}-\lambda\|_2^2$ (written $(\lambda_{\mathrm{QP}}-\lambda)^2$ on the page).
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1123, App. A, proof of Lemma 5, slack elimination

import Mathlib

namespace ALADIN.DualDecomp

open Matrix

/-- App. A, proof of Lemma 5, p. 1123: the minimization over the slack variable `s` in the dual of
QP (3.3). For `μ > 0` and `λ, λ_QP ∈ ℝᵐ`, every `s ∈ ℝᵐ` satisfies
`(μ/2)‖s‖²₂ − (λ_QP − λ)ᵀ s ≥ −(1/(2μ)) ‖λ_QP − λ‖²₂`, with equality iff `s = (λ_QP − λ)/μ`. -/
theorem slack_elimination {m : ℕ} (μ : ℝ) (hμ : 0 < μ) (lam lamQP : Fin m → ℝ) :
    (∀ s : Fin m → ℝ,
      -(1 / (2 * μ)) * ((lamQP - lam) ⬝ᵥ (lamQP - lam)) ≤
        μ / 2 * (s ⬝ᵥ s) - (lamQP - lam) ⬝ᵥ s) ∧
    (∀ s : Fin m → ℝ,
      μ / 2 * (s ⬝ᵥ s) - (lamQP - lam) ⬝ᵥ s =
          -(1 / (2 * μ)) * ((lamQP - lam) ⬝ᵥ (lamQP - lam)) ↔
        s = μ⁻¹ • (lamQP - lam)) := by sorry

end ALADIN.DualDecomp
