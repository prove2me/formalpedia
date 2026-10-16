-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_prop8_i_exists
-- name    : ClimateImpact.Uncertainty.prop8_i_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:40.852406+00:00
-- url     : https://prove2.me/theorems/78788600-bb98-4438-af08-6e83d87d7555
-- title:
--   Proposition 8(i), p. 38 — for every λ > 0 the fixed-point equation (23) has a positive solution (dates t ∈ [0, T))
-- statement:
--   Fix a date $t\in[0,T)$ and the model parameters of Proposition 7. Then for every intensity $\lambda>0$ the fixed-point equation (23),
--
--   $$
--   y=\exp\Big\{-\frac{\alpha\gamma^g}{\lambda}\Big[\mathbf 1^\top\theta_t(\psi_t(y))+\frac{y}{\gamma^r}\theta_t(\psi_t(y))^\top\Sigma_t^{-1}\theta_t(\psi_t(y))\Big]\Big\},
--   $$
--
--   has at least one positive solution $y$. Here $\psi_t(y)$ is the emission schedule (22) and $\theta_t$ the quadratic externality of Corollary 3.
--
--   This guarantees that the equilibrium with climate uncertainty and endogenous emissions exists.
--
--   **Formalization Note** (23) is formalized as footnote 25 derives it from (20); the printed (23) carries an extra factor $\alpha$ in the quadratic term, inconsistent with (20) and with the sign condition of (iii). The date is restricted to $t<T$. The page's argument uses $g^*(0)<\infty$, i.e. a finite schedule $\psi^i_t(0)=c^i_t/(\beta^c_t\kappa^c_t)$, which needs $\beta^c_t>0$, i.e. $t<T$. At $t=T$ the argument fails, and existence there is not claimed. The standing assumptions of the model are binders: $\rho>0$, $T>0$, $t\in[0,T]$ (the date is fixed and its subscript dropped), $0<\alpha<1$, $\gamma^r,\gamma^g>0$, $\kappa_t,\kappa^c_t,\kappa_{0,t}>0$ (Corollary 3: positive deterministic functions, the same for all companies by footnote 15), marginal abatement costs $c^i_t\ge 0$, and a positive definite covariance matrix $\Sigma_t$ (the page has $\Sigma_t=\sigma_t^\top\sigma_t$ with $\sigma_t$ invertible; only positive definiteness is used). $\alpha$ is a free parameter in $(0,1)$; the relation $\alpha=\gamma^r/(\gamma^r+\gamma^g)$ is not needed and is dropped, which makes the statement more general.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 8(i), p. 38; §6.5, proof of Proposition 8, p. 71

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proposition 8(i) (p. 38): for every `λ > 0` the fixed-point equation (23) has a positive
solution, at every date `t ∈ [0, T)`. -/
theorem prop8_i_exists {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Ico 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∀ lam : ℝ, 0 < lam → ∃ y : ℝ, IsYStar S γr γg lam ρ T t α κ κc κ₀ c y := by sorry

end ClimateImpact.Uncertainty
