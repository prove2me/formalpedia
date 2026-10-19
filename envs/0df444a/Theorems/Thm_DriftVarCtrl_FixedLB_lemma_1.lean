-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_1
-- name    : DriftVarCtrl.FixedLB.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:02.83244+00:00
-- url     : https://prove2.me/theorems/260747d9-edb6-4649-b89a-a7eb0e31bbc3
-- title:
--   Lemma 1, p. 14 — dᴸ₁ < dᴸ₂ < σ₂²/σ₁² < dᵁ₁ < dᵁ₂ < μ₂/μ₁ and dᴸ₂ > 0
-- statement:
--   Consider the two-control model with drifts $\mu_1, \mu_2 > 0$, volatilities $\sigma_1,\sigma_2 > 0$, upper boundary $U > 0$ and effective drifts $v_i = 2\mu_i/\sigma_i^2$, and assume $v_2 > v_1$. Let $d_1^L, d_1^U, d_2^L, d_2^U$ be the constants (11)–(14). Then
--   $$d_1^L < d_2^L < \frac{\sigma_2^2}{\sigma_1^2} < d_1^U < d_2^U < \frac{\mu_2}{\mu_1},\qquad d_2^L > 0 .$$
--
--   This fixes the relative position of the four lines $\Delta h_2 = d\,\Delta h_1$ of Theorem 2 for all parameter values, and is what makes the regions (7)–(10) cover the plane.
--
--   **Formalization Note.** The standing assumption $v_1 < v_2$ (p. 12) is the hypothesis `hv`; positivity of $\mu_i, \sigma_i, U$ is part of the model.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 14, Lemma 1, (15)–(16); proof pp. EC-2–EC-3

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants

namespace DriftVarCtrl.FixedLB

/-- Lemma 1 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 14, (15)–(16); proof pp. EC-2–EC-3). If `v₁ < v₂` (and `μ₁, μ₂ > 0`,
part of `Params`), then `dᴸ₁ < dᴸ₂ < σ₂²/σ₁² < dᵁ₁ < dᵁ₂ < μ₂/μ₁` and `dᴸ₂ > 0`. -/
theorem lemma_1 (p : Params) (hv : v p .one < v p .two) :
    dL1 p < dL2 p ∧ dL2 p < p.σ₂ ^ 2 / p.σ₁ ^ 2 ∧ p.σ₂ ^ 2 / p.σ₁ ^ 2 < dU1 p ∧
    dU1 p < dU2 p ∧ dU2 p < p.μ₂ / p.μ₁ ∧ 0 < dL2 p := by sorry

end DriftVarCtrl.FixedLB
