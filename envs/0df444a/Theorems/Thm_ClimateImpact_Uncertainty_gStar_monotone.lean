-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_gStar_monotone
-- name    : ClimateImpact.Uncertainty.gStar_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:38.408976+00:00
-- url     : https://prove2.me/theorems/00397a03-d932-4809-b386-eaad17643883
-- title:
--   §6.5, proof of Proposition 8(ii), pp. 71–72 — under (24), g* is monotonically increasing on (0, ∞)
-- statement:
--   Fix a date $t\in[0,T]$ and the model parameters of Proposition 7. Recall
--
--   $$
--   g^*(y)=\mathbf 1^\top\theta_t(\psi_t(y))+\frac{y}{\gamma^r}\,\theta_t(\psi_t(y))^\top\Sigma_t^{-1}\theta_t(\psi_t(y)),\qquad y>0.
--   $$
--
--   Assume condition (24): $\sum_j(\Sigma_t^{-1})_{ij}\,y\,\theta^j_t(\psi^j_t(y))\ge-\gamma^r/2$ for every company $i$ and every $y>0$. Then $g^*$ is monotonically increasing (nondecreasing) on $(0,\infty)$.
--
--   This is the step on which uniqueness (Proposition 8(ii)) and the comparative statics of Proposition 8(iii) rest. In the equivalent form (48), $-\lambda\log y=\alpha\gamma^g g^*(y)$, the left side strictly decreases in $y$.
--
--   **Formalization Note** (23) is formalized as footnote 25 derives it from (20); the printed (23) carries an extra factor $\alpha$ in the quadratic term, inconsistent with (20) and with the sign condition of (iii). Condition (24) is used with the bound $-\gamma^r/2$. That is the bound the argument of p. 72 needs once the derivative of the quadratic form carries the factor $2$ coming from the symmetry of $\Sigma_t^{-1}$. The printed bound is $-\gamma^r/\alpha$. The condition is imposed at the single date $t$. The standing assumptions of the model are binders: $\rho>0$, $T>0$, $t\in[0,T]$ (the date is fixed and its subscript dropped), $0<\alpha<1$, $\gamma^r,\gamma^g>0$, $\kappa_t,\kappa^c_t,\kappa_{0,t}>0$ (Corollary 3: positive deterministic functions, the same for all companies by footnote 15), marginal abatement costs $c^i_t\ge 0$, and a positive definite covariance matrix $\Sigma_t$ (the page has $\Sigma_t=\sigma_t^\top\sigma_t$ with $\sigma_t$ invertible; only positive definiteness is used). $\alpha$ is a free parameter in $(0,1)$; the relation $\alpha=\gamma^r/(\gamma^r+\gamma^g)$ is not needed and is dropped, which makes the statement more general.
-- source:
--   SSRN 3562534 (25 Jun 2021), §6.5, proof of Proposition 8(ii), pp. 71–72

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proof of Proposition 8(ii) (pp. 71–72): under condition (24), `g^*` is monotonically
increasing on `(0, ∞)`. -/
theorem gStar_monotone {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h24 : Cond24 S γr ρ T t α κ κc κ₀ c) :
    MonotoneOn (gStar S γr ρ T t α κ κc κ₀ c) (Set.Ioi 0) := by sorry

end ClimateImpact.Uncertainty
