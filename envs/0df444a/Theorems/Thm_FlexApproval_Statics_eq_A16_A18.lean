-- Prove2me | Theorems.Thm_FlexApproval_Statics_eq_A16_A18
-- name    : FlexApproval.Statics.eq_A16_A18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:45.55365+00:00
-- url     : https://prove2.me/theorems/dd94f1e3-59b0-4468-9386-3bdb89acd478
-- title:
--   Eqs. (A.16)–(A.18), p. 33 — λ̃·∂V′/∂λ̃ = V′ + WTP·Q_E·E[N_E]″·ψ_E·ψ_E′, which is ≤ 0 at the optimum
-- statement:
--   Under the standing assumptions, vary the arrival rate $\lambda$ keeping the other parameters fixed (so $\tilde\lambda$ varies proportionally to $\lambda$). Write $g'(\alpha)=e^{\delta\sqrt{I_n}\,\Phi^{-1}(1-\alpha)-\delta^2I_n/2}$, $\partial\psi_E/\partial\alpha=\tilde\lambda p\,g'(\alpha)/(K\mu_E)$ and $\partial^2\mathbb E[N_E]/\partial\psi_E^2=-2K/(1+\psi_E)^3$.
--
--   1. (A.17) For every $0<\alpha<1$, the map $\lambda\mapsto V'(\alpha)$ is differentiable at $\lambda$, and its derivative $D$ satisfies
--   $$\lambda D=V'(\alpha)+\mathrm{WTP}\cdot Q_E\,\frac{-2K}{(1+\psi_E(\alpha))^3}\,\psi_E(\alpha)\,\frac{\tilde\lambda p\,g'(\alpha)}{K\mu_E}.$$
--   2. (A.18) If $\alpha^*$ is an optimal policy, then at $\alpha=\alpha^*$
--   $$\lambda D=\mathrm{WTP}\cdot Q_E\,\frac{-2K}{(1+\psi_E(\alpha^*))^3}\,\psi_E(\alpha^*)\,\frac{\tilde\lambda p\,g'(\alpha^*)}{K\mu_E}\le0.$$
--
--   Since $\tilde\lambda=\lambda\mu_{CT}/(\mu_{CT}+\mu_{AB})$ is proportional to $\lambda$, $\lambda\,\partial/\partial\lambda=\tilde\lambda\,\partial/\partial\tilde\lambda$, so $\lambda D$ is the paper's $\tilde\lambda\,\partial V'/\partial\tilde\lambda$. By (A.8), $\alpha^*$ is nonincreasing in $\tilde\lambda$, hence in $\lambda$ and $\mu_{CT}$, and nondecreasing in $\mu_{AB}$.
--
--   **Formalization Note** The paper differentiates in $\tilde\lambda$, which is not a primitive parameter; the statement differentiates in $\lambda$ and multiplies by $\lambda$, which equals $\tilde\lambda\,\partial/\partial\tilde\lambda$. The second equality uses the first-order condition $V'(\alpha^*)=0$, as on the page.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 33, proof of Proposition 1, Eqs. (A.16)–(A.18)

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

open Cohen2019.Robust

/-- Eqs. (A.16)–(A.18), p. 33, with `λ̃` varied through `λ` (`λ̃` is proportional to `λ`, so
`λ ∂/∂λ = λ̃ ∂/∂λ̃`). (A.17): at every `0 < α < 1`,
`λ̃ ∂V′(α)/∂λ̃ = V′(α) + WTP·Q_E (∂²E[N_E]/∂ψ_E²) ψ_E(α) ∂ψ_E(α)/∂α`, with
`∂²E[N_E]/∂ψ_E² = −2K/(1 + ψ_E)³` and `∂ψ_E/∂α = λ̃ p gp(α)/(K µ_E)`. (A.18): at an optimal `α*` the first
term vanishes and the remaining term is `≤ 0`. -/
theorem eq_A16_A18 (P : Params) (hP : P.Standing) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, ∃ D : ℝ,
      HasDerivAt (fun x => deriv (V { P with lam := x }) α) D P.lam ∧
      P.lam * D = deriv (V P) α +
        P.WTP * P.QE * (-2 * (P.K : ℝ) / (1 + psiE P α) ^ 3) * psiE P α *
          (lamTilde P * P.p * gp (theta P) α / ((P.K : ℝ) * P.muE))) ∧
    (∀ a : ℝ, IsOptimal P a → ∃ D : ℝ,
      HasDerivAt (fun x => deriv (V { P with lam := x }) a) D P.lam ∧
      P.lam * D = P.WTP * P.QE * (-2 * (P.K : ℝ) / (1 + psiE P a) ^ 3) * psiE P a *
          (lamTilde P * P.p * gp (theta P) a / ((P.K : ℝ) * P.muE)) ∧
      P.WTP * P.QE * (-2 * (P.K : ℝ) / (1 + psiE P a) ^ 3) * psiE P a *
          (lamTilde P * P.p * gp (theta P) a / ((P.K : ℝ) * P.muE)) ≤ 0) := by sorry

end FlexApproval.Statics
