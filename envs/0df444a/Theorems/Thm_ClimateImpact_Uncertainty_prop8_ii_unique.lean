-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_prop8_ii_unique
-- name    : ClimateImpact.Uncertainty.prop8_ii_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:03.31708+00:00
-- url     : https://prove2.me/theorems/b150f293-fece-4a85-a19f-735f87dd49bd
-- title:
--   Proposition 8(ii), p. 38 — under condition (24) the positive solution of (23) is unique
-- statement:
--   Fix a date $t\in[0,T]$ and the model parameters of Proposition 7. Assume condition (24): for every company $i$ and every $y>0$,
--
--   $$
--   \sum_{j=1}^n(\Sigma_t^{-1})_{ij}\,y\,\theta^j_t(\psi^j_t(y))\ge-\frac{\gamma^r}{2}.
--   $$
--
--   Then for every $\lambda>0$, any two positive solutions $y_1,y_2$ of the fixed-point equation (23) coincide.
--
--   Together with Proposition 8(i), this makes $y^*_\lambda$ well defined at every date $t<T$.
--
--   **Formalization Note** (23) is formalized as footnote 25 derives it from (20); the printed (23) carries an extra factor $\alpha$ in the quadratic term, inconsistent with (20) and with the sign condition of (iii). The bound in (24) is $-\gamma^r/2$ instead of the printed $-\gamma^r/\alpha$, for the reason given in the definition of `Cond24`. Whether uniqueness holds under the printed bound is not claimed. The page's further sentence, that the solution is unique in the regime $\lambda\to\infty$, has no proof in the paper and is not formalized. The standing assumptions of the model are binders: $\rho>0$, $T>0$, $t\in[0,T]$ (the date is fixed and its subscript dropped), $0<\alpha<1$, $\gamma^r,\gamma^g>0$, $\kappa_t,\kappa^c_t,\kappa_{0,t}>0$ (Corollary 3: positive deterministic functions, the same for all companies by footnote 15), marginal abatement costs $c^i_t\ge 0$, and a positive definite covariance matrix $\Sigma_t$ (the page has $\Sigma_t=\sigma_t^\top\sigma_t$ with $\sigma_t$ invertible; only positive definiteness is used). $\alpha$ is a free parameter in $(0,1)$; the relation $\alpha=\gamma^r/(\gamma^r+\gamma^g)$ is not needed and is dropped, which makes the statement more general.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 8(ii), (24), p. 38; §6.5, pp. 71–72

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proposition 8(ii) (p. 38): under condition (24), the positive solution of (23) is unique. -/
theorem prop8_ii_unique {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h24 : Cond24 S γr ρ T t α κ κc κ₀ c) :
    ∀ lam : ℝ, 0 < lam → ∀ y₁ y₂ : ℝ, IsYStar S γr γg lam ρ T t α κ κc κ₀ c y₁ →
      IsYStar S γr γg lam ρ T t α κ κc κ₀ c y₂ → y₁ = y₂ := by sorry

end ClimateImpact.Uncertainty
