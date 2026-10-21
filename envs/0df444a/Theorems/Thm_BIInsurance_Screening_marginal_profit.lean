-- Prove2me | Theorems.Thm_BIInsurance_Screening_marginal_profit
-- name    : BIInsurance.Screening.marginal_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:36.567825+00:00
-- url     : https://prove2.me/theorems/fd199c81-3dff-4366-a75d-7515835b0827
-- title:
--   Proof of Proposition 1(ii), p. 33 — d/ds E[π^I_i] = ρ(1+λ)(T−τ−w)p{K − γE_δ[ξ(K, µ_i, δ)] + γ ln(A/(A−c))} ≥ 0 when e∗ ≠ 1
-- statement:
--   Assume the standing assumptions, let $\mu\ge\mu_L$, $y\in\mathbb R$ and $s\in[0,\bar s]$, and suppose the optimal efforts for both forecast updates are interior at $s$: $e^*_{\mu+\delta_H}(s)\ne1$ and $e^*_{\mu+\delta_L}(s)\ne1$. Write $A(s)=wp+(T-\tau-w)p(1-s)$ and $E_\delta[\xi(K,\mu,\delta)]=\beta\,\xi(K,\mu,\delta_H)+(1-\beta)\,\xi(K,\mu,\delta_L)$. Then the expected profit with insurance is differentiable in $s$ at $s$, with
--
--   $$
--   \frac{d}{ds}E_{\delta,Z}\big[\pi^I_i(K,y,s)\big]=\rho(1+\lambda)(T-\tau-w)p\Big\{K-\gamma E_\delta[\xi(K,\mu,\delta)]+\gamma\ln\frac{A(s)}{A(s)-c}\Big\}\ \ge 0 .
--   $$
--
--   This explicit marginal value of coverage is the formula behind Propositions 1(ii) and 2; because $\xi$ is strictly increasing in $\mu$, it shows that a lower early forecast has a higher marginal value of coverage.
--
--   **Formalization Note** The page computes the derivative for $\mu=\mu_i$; here every $\mu\ge\mu_L$ is allowed. The first line of the page's display writes $\beta\rho$ for $(1-\beta)\rho$ on the $L$ term, a typo that the next line corrects; the statement uses the corrected value.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 33, proof of Proposition 1(ii)

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem marginal_profit (P : Params) (hS : P.Standing) (mu y s : ℝ) (hmu : P.muL ≤ mu)
    (hs : s ∈ Set.Icc 0 P.sbar)
    (hH : eStar P (mu + P.dH) s ≠ 1) (hL : eStar P (mu + P.dL) s ≠ 1) :
    HasDerivAt (fun s' => EpiI P mu y s')
      (P.ρ * (1 + P.lam) * ((P.T : ℝ) - P.τ - P.w) * P.p *
        (P.K - P.γ * Exi P mu + P.γ * Real.log (Aeff P s / (Aeff P s - P.c)))) s ∧
      0 ≤ P.ρ * (1 + P.lam) * ((P.T : ℝ) - P.τ - P.w) * P.p *
        (P.K - P.γ * Exi P mu + P.γ * Real.log (Aeff P s / (Aeff P s - P.c))) := by sorry

end BIInsurance.Screening
