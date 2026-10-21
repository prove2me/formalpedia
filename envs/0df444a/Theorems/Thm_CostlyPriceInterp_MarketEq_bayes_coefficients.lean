-- Prove2me | Theorems.Thm_CostlyPriceInterp_MarketEq_bayes_coefficients
-- name    : CostlyPriceInterp.MarketEq.bayes_coefficients
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:27.770287+00:00
-- url     : https://prove2.me/theorems/02fa245f-9c1e-4d17-990d-368316097f39
-- title:
--   Proof of Proposition 1, p. 55 — the Bayes coefficients β_s, β_p, β_z of (16) in closed form
-- statement:
--   Assume the standing assumptions $\tau_v,\tau_\xi,\tau_\varepsilon,\tau_e,\tau_u,\tau_\eta,\gamma>0$ and let $\alpha\in\mathbb R$ be the price-signal loading on the noise $\tilde u$. Let $\Sigma(\alpha)$ be the covariance matrix of investor $i$'s signals $(\tilde s_i,\tilde s_{p,i},\tilde z_i)$ and $c$ their covariance with $\tilde v$, and let $\tau_p = \tau_p(\alpha)$ be given by (15). Then $\Sigma(\alpha)$ is nonsingular, and the conditional-mean coefficients $(\beta_s,\beta_p,\beta_z) = \Sigma(\alpha)^{-1}c$ are
--   $$\beta_s = \frac{\tau_\varepsilon}{\tau_v+\tau_\varepsilon+\tau_p},\qquad \beta_p = \frac{\tau_p}{\tau_v+\tau_\varepsilon+\tau_p},\qquad \beta_z = -\frac{\tau_\eta(\tau_e+\tau_u+\alpha\tau_e)}{\tau_e\tau_u+\tau_e\tau_\eta+\tau_u\tau_\eta}\cdot\frac{\tau_p}{\tau_v+\tau_\varepsilon+\tau_p}.$$
--
--   This is the Bayesian-updating step of the equilibrium construction: it turns the abstract Gaussian projection into the explicit weights an investor places on her private signal, her reading of the price and her interpretation signal.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), p. 55 (PDF 54), proof of Proposition 1, the expressions of β_{s,i}, β_{p,i}, β_{z,i} with τ_{η_i} = τ_η; τ_p from eq. (15), p. 18 (PDF 20)

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

namespace CostlyPriceInterp.MarketEq

/-- Proof of Proposition 1, p. 55 (PDF 54): Σ(α) is invertible and the Gaussian conditional-mean
coefficients (β_s, β_p, β_z) = Σ(α)⁻¹c of (16) are the printed closed forms, with τ_p of (15). -/
theorem bayes_coefficients (P : Params) (hP : P.Standing) (α : ℝ) :
    (sigCov P α).det ≠ 0 ∧
    bayesCoef P α =
      ![P.teps / (P.tv + P.teps + tauP P α),
        tauP P α / (P.tv + P.teps + tauP P α),
        -(P.teta * (P.te + P.tu + α * P.te) / (P.te * P.tu + P.te * P.teta + P.tu * P.teta)) *
          (tauP P α / (P.tv + P.teps + tauP P α))] := by sorry
end CostlyPriceInterp.MarketEq
