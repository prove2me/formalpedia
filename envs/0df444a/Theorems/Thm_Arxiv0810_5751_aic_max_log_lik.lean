-- Prove2me | Theorems.Thm_Arxiv0810_5751_aic_max_log_lik
-- name    : Arxiv0810_5751.aic_max_log_lik
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:45:19.516322+00:00
-- url     : https://prove2.me/theorems/51325d83-2bf5-4a77-8d81-9945578421fb
-- title:
--   Eq. (19): $\mathrm{AIC}(K)=-2L(\hat\theta)+2(2P)$ with $L(\hat\theta)$ the maximised log-likelihood
-- statement:
--   Let $\mathbf y\in\mathbb C^M$ and let $\mathbf s_i:\mathbb C^P\to\mathbb C^M$, $i=1,\dots,K$, be the contributions of a $K$-source model with $P$ complex ($2P$ real) parameters. Let $\hat{\boldsymbol\theta}$ be the least-squares estimate of eq. (5),
--
--   $$\hat{\boldsymbol\theta}\in\arg\min_{\boldsymbol\theta\in\mathbb C^P}\Big\|\mathbf y-\sum_{i=1}^K\mathbf s_i(\boldsymbol\theta)\Big\|^2,$$
--
--   and suppose its residual is nonzero. Then the value $L(\hat{\boldsymbol\theta})$ of eq. (18) is the maximum of the white-noise log-likelihood $L(\boldsymbol\theta,\sigma^2)$ over all $\boldsymbol\theta\in\mathbb C^P$ and $\sigma^2>0$, so that
--
--   $$\mathrm{AIC}(K)=-2L(\hat{\boldsymbol\theta})+2(2P)=-2\max_{\boldsymbol\theta,\,\sigma^2>0}L(\boldsymbol\theta,\sigma^2)+2(2P)$$
--
--   is Akaike's criterion for the $K$-source model. The paper selects the $K$ minimising $\mathrm{AIC}(K)$.
--
--   **Formalization Note** The paper writes eq. (19) as a definition. What is stated here is the fact it rests on, that $L(\hat{\boldsymbol\theta})$ is the maximised log-likelihood. The selection rule itself is a procedure and is not a statement. As in the paper, the penalty counts the $2P$ real parameters and not $\sigma^2$. A nonzero residual at $\hat{\boldsymbol\theta}$ is assumed; otherwise the likelihood is unbounded.
-- source:
--   Yatawatta, Zaroubi, de Bruyn, Koopmans and Noordam, Radio interferometric calibration using the SAGE algorithm, arXiv:0810.5751v1 (2008), claim c008; Section IV (Statistical Model Order Selection), eqs. (5), (16)-(19), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv0810_5751_Basic

open MeasureTheory Matrix
open scoped ComplexOrder

namespace Arxiv0810_5751

theorem aic_max_log_lik {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θhat : Fin P → ℂ) (hmin : ∀ θ : Fin P → ℂ, residSq y s θhat ≤ residSq y s θ)
    (hr : residual y s θhat ≠ 0) :
    IsGreatest {L : ℝ | ∃ (θ : Fin P → ℂ) (σ2 : ℝ), 0 < σ2 ∧ whiteLogLik σ2 y s θ = L}
        (concLogLik y s θhat) ∧
    aic y s θhat =
      -2 * sSup {L : ℝ | ∃ (θ : Fin P → ℂ) (σ2 : ℝ), 0 < σ2 ∧ whiteLogLik σ2 y s θ = L} +
        2 * (2 * P) := by sorry

end Arxiv0810_5751
