-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_prop8_iii_uncertainty_raises_emissions
-- name    : ClimateImpact.Uncertainty.prop8_iii_uncertainty_raises_emissions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:54.185619+00:00
-- url     : https://prove2.me/theorems/f501046c-ff81-46d3-ba21-506125bc22c8
-- title:
--   Proposition 8(iii), pp. 38–39 — sign of θ(ψ^{*,0})ᵀN^g fixes the monotonicity of λ ↦ y*_λ, lim y*_λ = 1, and the direction of the emission response
-- statement:
--   Fix a date $t\in[0,T]$ and the model parameters of Proposition 7. Assume condition (24) at $t$:
--
--   $$
--   \sum_{j=1}^n(\Sigma_t^{-1})_{ij}\,y\,\theta^j_t(\psi^j_t(y))\ge-\frac{\gamma^r}{2}\qquad\text{for all } i \text{ and all } y>0.
--   $$
--
--   Let $\lambda\mapsto y^*_\lambda$ be the solution map of the fixed-point equation (23): for every $\lambda>0$, $y^*_\lambda>0$ solves (23). Let $\psi^{*,0,i}_t=c^i_t(\beta^c_t\kappa^c_t+\alpha\beta_t\kappa_t)^{-1}$ be the equilibrium emission schedule without climate uncertainty (13), and $N^g_t=\alpha(\mathbf 1+\frac{1}{\gamma^r}\Sigma_t^{-1}\theta_t(\psi^{*,0}_t))$ the corresponding green portfolio (11). Write $\psi^{*,i}_t=c^i_t/(\alpha\beta_t\kappa_t y^*_\lambda+\beta^c_t\kappa^c_t)$ for the equilibrium schedule (22). Then:
--
--   1. if $\theta_t(\psi^{*,0}_t)^\top N^g_t>0$, then $y^*_\lambda>0$, $\lambda\mapsto y^*_\lambda$ is strictly increasing on $(0,\infty)$, $y^*_\lambda\to1$ as $\lambda\to\infty$, and every $\psi^{*,i}_t$ is nonincreasing in $\lambda$: more climate uncertainty (smaller $\lambda$) raises emissions;
--   2. if $\theta_t(\psi^{*,0}_t)^\top N^g_t<0$, then $y^*_\lambda>0$, $\lambda\mapsto y^*_\lambda$ is strictly decreasing on $(0,\infty)$, $y^*_\lambda\to1$, and every $\psi^{*,i}_t$ is nondecreasing in $\lambda$: more climate uncertainty lowers emissions;
--   3. if $\theta_t(\psi^{*,0}_t)^\top N^g_t=0$, then $y^*_\lambda=1$ and $\psi^*_t$ equals its value at $y=1$ for every $\lambda>0$: climate uncertainty does not affect emissions.
--
--   This is the paper's main result on climate uncertainty. When the green portfolio is green, which is the common case by Lemma 1, uncertainty about future climate externalities pushes companies to emit more.
--
--   **Formalization Note** (23) is formalized as footnote 25 derives it from (20); the printed (23) carries an extra factor $\alpha$ in the quadratic term, inconsistent with (20) and with the sign condition of (iii). Condition (24) is used with the bound $-\gamma^r/2$ that the argument of p. 72 needs (see `Cond24`), and only at the date $t$. The solution map enters only through the hypothesis that each $y^*_\lambda$ solves (23); uniqueness is not assumed, it follows from (24). The schedule's monotonicity in $\lambda$ is weak, because at $t=0$ ($\beta_0=0$) or when $c^i_t=0$ the schedule does not depend on $y$. The standing assumptions of the model are binders: $\rho>0$, $T>0$, $t\in[0,T]$ (the date is fixed and its subscript dropped), $0<\alpha<1$, $\gamma^r,\gamma^g>0$, $\kappa_t,\kappa^c_t,\kappa_{0,t}>0$ (Corollary 3: positive deterministic functions, the same for all companies by footnote 15), marginal abatement costs $c^i_t\ge 0$, and a positive definite covariance matrix $\Sigma_t$ (the page has $\Sigma_t=\sigma_t^\top\sigma_t$ with $\sigma_t$ invertible; only positive definiteness is used). $\alpha$ is a free parameter in $(0,1)$; the relation $\alpha=\gamma^r/(\gamma^r+\gamma^g)$ is not needed and is dropped, which makes the statement more general.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 8(iii), pp. 38–39; §6.5, p. 72

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proposition 8(iii) (pp. 38–39): under condition (24), the sign of `θ_t(ψ^{*,0}_t)ᵀ N^g_t`
decides whether `λ ↦ y^*_λ` increases or decreases to `1`, and with it whether more climate
uncertainty (smaller `λ`) raises or lowers the equilibrium emission schedule (22). -/
theorem prop8_iii_uncertainty_raises_emissions {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h24 : Cond24 S γr ρ T t α κ κc κ₀ c)
    (Y : ℝ → ℝ) (hY : ∀ lam : ℝ, 0 < lam → IsYStar S γr γg lam ρ T t α κ κc κ₀ c (Y lam)) :
    (0 < ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 →
      (∀ lam : ℝ, 0 < lam → 0 < Y lam) ∧ StrictMonoOn Y (Set.Ioi 0) ∧
        Filter.Tendsto Y Filter.atTop (nhds 1) ∧
        ∀ i, AntitoneOn (fun lam => schedule ρ T t α κ κc c (Y lam) i) (Set.Ioi 0)) ∧
    (ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 < 0 →
      (∀ lam : ℝ, 0 < lam → 0 < Y lam) ∧ StrictAntiOn Y (Set.Ioi 0) ∧
        Filter.Tendsto Y Filter.atTop (nhds 1) ∧
        ∀ i, MonotoneOn (fun lam => schedule ρ T t α κ κc c (Y lam) i) (Set.Ioi 0)) ∧
    (ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 = 0 →
      ∀ lam : ℝ, 0 < lam → Y lam = 1 ∧ schedule ρ T t α κ κc c (Y lam) = schedule ρ T t α κ κc c 1) := by sorry

end ClimateImpact.Uncertainty
