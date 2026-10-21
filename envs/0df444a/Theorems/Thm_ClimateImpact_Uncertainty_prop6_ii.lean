-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_prop6_ii
-- name    : ClimateImpact.Uncertainty.prop6_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:14.863693+00:00
-- url     : https://prove2.me/theorems/24df8e2a-d4a3-4643-ad55-d78eb9da34c1
-- title:
--   Proposition 6(ii), pp. 34–35 — if θᵀN^g > 0, y_λ is positive, increasing, → 1; more uncertainty shifts green investors to brown assets and lowers brown returns
-- statement:
--   Let $\Sigma$ be positive definite, $0<\alpha<1$, $\gamma^r,\gamma^g>0$, and fix the externality vector $\theta=\theta_t(\psi_t)$ of a given emission schedule. Let $\lambda\mapsto y_\lambda$ be the solution map of (20): for every $\lambda>0$, $y_\lambda>0$ solves (20). Write $N^g=\alpha(\mathbf 1+\frac{1}{\gamma^r}\Sigma^{-1}\theta)$ for the green portfolio without climate uncertainty, $N^{g,\lambda}=\alpha(\mathbf 1+\frac{y_\lambda}{\gamma^r}\Sigma^{-1}\theta)$ for the one with uncertainty level $\lambda$, and $\mu_\lambda=\gamma^*\Sigma\mathbf 1-\alpha y_\lambda\theta$ for the expected returns (18).
--
--   If $\theta^\top N^g>0$, then:
--
--   1. $y_\lambda>0$ for all $\lambda>0$;
--   2. $\lambda\mapsto y_\lambda$ is strictly increasing on $(0,\infty)$;
--   3. $y_\lambda\to1$ as $\lambda\to\infty$;
--   4. $\lambda\mapsto\theta^\top N^{g,\lambda}$ is strictly increasing, so as uncertainty grows ($\lambda$ decreases) the green portfolio moves towards brown assets;
--   5. for every brown company $i$ ($\theta^i<0$), $\lambda\mapsto\mu^i_\lambda$ is strictly increasing, so its expected return falls as $\lambda$ decreases;
--   6. for every green company $i$ ($\theta^i>0$), $\lambda\mapsto\mu^i_\lambda$ is strictly decreasing, so its expected return rises as $\lambda$ decreases.
--
--   This is the paper's main case (Lemma 1): climate uncertainty dampens the externality premium.
--
--   **Formalization Note** The solution map enters only through the hypothesis that each $y_\lambda$ solves (20); its values at $\lambda\le0$ play no role. "Positive" and "monotonically increasing/decreasing" are read as $y_\lambda>0$ and strict monotonicity on $(0,\infty)$. A company $i$ is **brown** when $\theta^i<0$ and **green** when $\theta^i>0$ (p. 18). "Reallocate their wealth towards brown (green) assets" is read as "the climate externality $\theta^\top N^{g,\lambda}$ of the green portfolio decreases (increases) as $\lambda$ decreases". The page makes no per-asset claim, and the individual holdings move with $(\Sigma^{-1}\theta)^i$, not with $\theta^i$. $\alpha\in(0,1)$ is free; $\Sigma$ is positive definite.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 6(ii), pp. 34–35; §6.4, pp. 69–70

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_Portfolio
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proposition 6(ii) (pp. 34–35): if the green portfolio without climate uncertainty has
positive climate externalities, `λ ↦ y_λ` is positive, strictly increasing and tends to `1`; as
`λ` decreases, the climate externality of the green portfolio decreases, the expected returns of
the brown companies decrease and those of the green companies increase. -/
theorem prop6_ii {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (θ : Fin n → ℝ)
    (Y : ℝ → ℝ) (hY : ∀ lam : ℝ, 0 < lam → IsYLambda S α γr γg lam θ (Y lam))
    (hpos : 0 < θ ⬝ᵥ greenPortfolio S α γr θ 1) :
    (∀ lam : ℝ, 0 < lam → 0 < Y lam) ∧
    StrictMonoOn Y (Set.Ioi 0) ∧
    Filter.Tendsto Y Filter.atTop (nhds 1) ∧
    StrictMonoOn (fun lam => θ ⬝ᵥ greenPortfolio S α γr θ (Y lam)) (Set.Ioi 0) ∧
    (∀ i, θ i < 0 → StrictMonoOn (fun lam => expectedReturn S α γr γg θ (Y lam) i) (Set.Ioi 0)) ∧
    (∀ i, 0 < θ i → StrictAntiOn (fun lam => expectedReturn S α γr γg θ (Y lam) i) (Set.Ioi 0)) := by sorry

end ClimateImpact.Uncertainty
