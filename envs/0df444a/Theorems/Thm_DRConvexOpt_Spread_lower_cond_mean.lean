-- Prove2me | Theorems.Thm_DRConvexOpt_Spread_lower_cond_mean
-- name    : DRConvexOpt.Spread.lower_cond_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:41.848995+00:00
-- url     : https://prove2.me/theorems/759eecba-d017-4b5e-b79e-7c65ee7e59fb
-- title:
--   Proof of Proposition 2, pp. 40–41 — for P ∈ 𝒫, E_P[fᵀz̃ | fᵀz̃ < θ] ≥ (1 − ρ)⁻¹E_P[−ṽ] + θ
-- statement:
--   Let $f\in\mathbb R^P$, $\theta\in\mathbb R$, $\sigma\ge0$ and $\rho\in(0,1)$, and let $\mathcal P$ be the lifted ambiguity set of Proposition 2: distributions $\mathbb P$ of $(\tilde z,\tilde u,\tilde v,\tilde w)$ on $\mathbb R^P\times\mathbb R^3$ with $\mathbb E_{\mathbb P}[\tilde w]=\sigma$, $\mathbb P[f^\top\tilde z\ge\theta]=\rho$ and, almost surely, $f^\top\tilde z=\theta+\tilde u-\tilde v$, $\tilde w\ge\rho^{-1}\tilde u+(1-\rho)^{-1}\tilde v$, $\tilde u,\tilde v\ge0$. Then every $\mathbb P\in\mathcal P$ satisfies
--
--   $$
--   \mathbb E_{\mathbb P}[f^\top\tilde z\mid f^\top\tilde z<\theta]\ge(1-\rho)^{-1}\,\mathbb E_{\mathbb P}[-\tilde v]+\theta .
--   $$
--
--   This is the lower half of the bound on the absolute mean spread of any member of $\mathcal P$.
--
--   **Formalization Note** The conditional means are elementary conditional expectations, $\mathbb E_{\mathbb Q}[f^\top\tilde z\mid A]=\mathbb E_{\mathbb Q}[f^\top\tilde z\,\mathbf 1_A]/\mathbb Q[A]$; both events have probability $\rho$ or $1-\rho$, which are positive because $\rho\in(0,1)$, so no division by zero occurs. An outcome is $\omega=(z,(u,v,w))\in\mathbb R^P\times(\mathbb R\times\mathbb R\times\mathbb R)$, with $\tilde u,\tilde v,\tilde w$ the projections `uOf`, `vOf`, `wOf`; the marginal $\Pi_{\tilde z}\mathbb P$ is the push-forward of $\mathbb P$ under the first projection. Integrability of $\tilde u$, $\tilde v$ and $f^\top\tilde z$ under $\mathbb P$ is not assumed: it follows from $0\le\tilde u\le\rho\tilde w$, $0\le\tilde v\le(1-\rho)\tilde w$ almost surely and the integrability of $\tilde w$. The conditional mean is that of the marginal $\Pi_{\tilde z}\mathbb P$. The standing hypothesis $\sigma\ge0$ is kept.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 40–41, proof of Proposition 2, second chain display

import Mathlib
import Definitions.Def_DRConvexOpt_Spread_Setting

namespace DRConvexOpt.Spread

open MeasureTheory

/-- Proof of Proposition 2, pp. 40–41: for every `P ∈ 𝒫`,
`E_P[fᵀz̃ | fᵀz̃ < θ] ≥ (1 − ρ)⁻¹ E_P[−ṽ] + θ`. -/
theorem lower_cond_mean {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) (hσ : 0 ≤ σ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (μ : Measure ((Fin nP → ℝ) × (ℝ × ℝ × ℝ)))
    (hμ : μ ∈ liftedSpreadSet f θ σ ρ) :
    (1 - ρ)⁻¹ * ∫ ω, -vOf ω ∂μ + θ ≤ condMeanLt (μ.map Prod.fst) f θ := by sorry

end DRConvexOpt.Spread
