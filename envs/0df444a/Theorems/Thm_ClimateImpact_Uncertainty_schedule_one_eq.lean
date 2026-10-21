-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_schedule_one_eq
-- name    : ClimateImpact.Uncertainty.schedule_one_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:43.746663+00:00
-- url     : https://prove2.me/theorems/e04cdeba-abfb-4625-87d7-eec971263527
-- title:
--   §6.5, proof of Proposition 8(iii), p. 72 — ψ*_t(1) = ψ^{*,0}_t, and αg*(1) = θ_t(ψ^{*,0}_t)ᵀN^g_t
-- statement:
--   Fix a date $t\in[0,T]$ and the model parameters of Proposition 7. Then:
--
--   1. at $y=1$ the emission schedule (22) is the schedule (13) without climate uncertainty: for every company $i$,
--   $$
--   \psi^i_t(1)=\frac{c^i_t}{\beta^c_t\kappa^c_t+\alpha\beta_t\kappa_t}=\psi^{*,0,i}_t;
--   $$
--   2. the value at $1$ of $g^*$ has the sign of the climate externality of the green portfolio without uncertainty:
--   $$
--   \alpha\,g^*(1)=\theta_t(\psi^{*,0}_t)^\top N^g_t,\qquad N^g_t=\alpha\Big(\mathbf 1+\frac{1}{\gamma^r}\Sigma_t^{-1}\theta_t(\psi^{*,0}_t)\Big).
--   $$
--
--   The second identity is what turns the case distinction of Proposition 8(iii) on the sign of $\theta_t(\psi^{*,0}_t)^\top N^g_t$ into a case distinction on the sign of $g^*(1)$.
--
--   **Formalization Note** (23) is formalized as footnote 25 derives it from (20); the printed (23) carries an extra factor $\alpha$ in the quadratic term, inconsistent with (20) and with the sign condition of (iii). The identity in item 2 holds for this corrected $g^*$ and fails for the printed one. The standing assumptions of the model are binders: $\rho>0$, $T>0$, $t\in[0,T]$ (the date is fixed and its subscript dropped), $0<\alpha<1$, $\gamma^r,\gamma^g>0$, $\kappa_t,\kappa^c_t,\kappa_{0,t}>0$ (Corollary 3: positive deterministic functions, the same for all companies by footnote 15), marginal abatement costs $c^i_t\ge 0$, and a positive definite covariance matrix $\Sigma_t$ (the page has $\Sigma_t=\sigma_t^\top\sigma_t$ with $\sigma_t$ invertible; only positive definiteness is used). $\alpha$ is a free parameter in $(0,1)$; the relation $\alpha=\gamma^r/(\gamma^r+\gamma^g)$ is not needed and is dropped, which makes the statement more general.
-- source:
--   SSRN 3562534 (25 Jun 2021), §6.5, proof of Proposition 8(iii), p. 72; (11), p. 18; (13), p. 20

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proof of Proposition 8(iii) (p. 72): at `y = 1` the schedule (22) is the schedule (13)
without climate uncertainty, and `α g^*(1)` equals `θ_t(ψ^{*,0}_t)ᵀ N^g_t`. -/
theorem schedule_one_eq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∀ i, schedule ρ T t α κ κc c 1 i = ClimateImpact.Interaction.noInteractionRate ρ T α κ κc (c i) t) ∧
    α * gStar S γr ρ T t α κ κc κ₀ c 1 =
      ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 := by sorry

end ClimateImpact.Uncertainty
