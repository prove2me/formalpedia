-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_2
-- name    : ChurnServiceMode.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:33.674815+00:00
-- url     : https://prove2.me/theorems/a398eef5-4bfb-424c-990e-e165f5a1c22e
-- title:
--   Lemma 2 — uniqueness of the risk-averse threshold $\theta_b$
-- statement:
--   Let $\mu_R,\mu_S,\sigma_R>0$ with $\mu_R>\mu_S$. Then the equation
--   $$\frac{\mu_R\sqrt\pi(\mu_S-\theta)}{\sigma_R}\exp\Bigl(\frac{(\theta-\mu_R)^2}{\sigma_R^2}\Bigr)\Bigl(1-\operatorname{erf}\Bigl(\frac{\theta-\mu_R}{\sigma_R}\Bigr)\Bigr)+\mu_S=0$$
--   has exactly one solution $\theta\in(\mu_S,\infty)$, called $\theta_b$. (For $\mu_R\le\mu_S$ the paper sets $\theta_b=\infty$.)
--
--   $\theta_b$ is the upper end of the risk-averse region $[q,\theta_b]$ of the optimal policy.
--
--   Differences from the source:
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - encoding: "If µR ≤ µS, let θb = ∞" → part of the definition IsThetaB, not of this statement; reason: it defines θb and claims nothing
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 2, p.9 (PDF p.9)

import Mathlib
import Definitions.Def_ChurnServiceMode_optPolicy

namespace ChurnServiceMode

/-- **Lemma 2** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.9). If `μR > μS`, the equation
`μR √π (μS − θ)/σR · exp((θ − μR)²/σR²) · (1 − erf((θ − μR)/σR)) + μS = 0`
has exactly one solution `θ` in `(μS, ∞)` (labelled `θb`; for `μR ≤ μS` the paper sets
`θb = ∞`). -/
theorem lemma_2 (p : Params) (h : p.μS < p.μR) :
    ∃! θ : ℝ, p.μS < θ ∧ lemma2Fn p θ = 0 := by sorry

end ChurnServiceMode
