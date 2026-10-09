-- Prove2me | Theorems.Thm_DRConvexOpt_Spread_spread_le_sigma
-- name    : DRConvexOpt.Spread.spread_le_sigma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:42.304119+00:00
-- url     : https://prove2.me/theorems/f1d1191a-6a04-4d0d-a988-593f1e97da62
-- title:
--   Proof of Proposition 2, p. 41 — for P ∈ 𝒫 the spread is ≤ ρ⁻¹E_P[ũ] + (1 − ρ)⁻¹E_P[ṽ] ≤ E_P[w̃] = σ
-- statement:
--   Let $f\in\mathbb R^P$, $\theta\in\mathbb R$, $\sigma\ge0$ and $\rho\in(0,1)$, and let $\mathcal P$ be the lifted ambiguity set of Proposition 2: distributions $\mathbb P$ of $(\tilde z,\tilde u,\tilde v,\tilde w)$ on $\mathbb R^P\times\mathbb R^3$ with $\mathbb E_{\mathbb P}[\tilde w]=\sigma$, $\mathbb P[f^\top\tilde z\ge\theta]=\rho$ and, almost surely, $f^\top\tilde z=\theta+\tilde u-\tilde v$, $\tilde w\ge\rho^{-1}\tilde u+(1-\rho)^{-1}\tilde v$, $\tilde u,\tilde v\ge0$. Then every $\mathbb P\in\mathcal P$ satisfies
--
--   $$
--   \mathbb E_{\mathbb P}[f^\top\tilde z\mid f^\top\tilde z\ge\theta]-\mathbb E_{\mathbb P}[f^\top\tilde z\mid f^\top\tilde z<\theta]\le\rho^{-1}\mathbb E_{\mathbb P}[\tilde u]+(1-\rho)^{-1}\mathbb E_{\mathbb P}[\tilde v]\le\mathbb E_{\mathbb P}[\tilde w]=\sigma .
--   $$
--
--   The chain shows that every member of $\mathcal P$ has absolute mean spread at most $\sigma$.
--
--   **Formalization Note** The conditional means are elementary conditional expectations, $\mathbb E_{\mathbb Q}[f^\top\tilde z\mid A]=\mathbb E_{\mathbb Q}[f^\top\tilde z\,\mathbf 1_A]/\mathbb Q[A]$; both events have probability $\rho$ or $1-\rho$, which are positive because $\rho\in(0,1)$, so no division by zero occurs. An outcome is $\omega=(z,(u,v,w))\in\mathbb R^P\times(\mathbb R\times\mathbb R\times\mathbb R)$, with $\tilde u,\tilde v,\tilde w$ the projections `uOf`, `vOf`, `wOf`; the marginal $\Pi_{\tilde z}\mathbb P$ is the push-forward of $\mathbb P$ under the first projection. Integrability of $\tilde u$, $\tilde v$ and $f^\top\tilde z$ under $\mathbb P$ is not assumed: it follows from $0\le\tilde u\le\rho\tilde w$, $0\le\tilde v\le(1-\rho)\tilde w$ almost surely and the integrability of $\tilde w$. The chain is stated as the conjunction of its two inequalities and its final identity; the conditional means are those of $\Pi_{\tilde z}\mathbb P$.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 41, proof of Proposition 2, display after “From the definition of the ambiguity set 𝒫”

import Mathlib
import Definitions.Def_DRConvexOpt_Spread_Setting

namespace DRConvexOpt.Spread

open MeasureTheory

/-- Proof of Proposition 2, p. 41: for every `P ∈ 𝒫`,
`E_P[fᵀz̃ | fᵀz̃ ≥ θ] − E_P[fᵀz̃ | fᵀz̃ < θ] ≤ ρ⁻¹E_P[ũ] + (1 − ρ)⁻¹E_P[ṽ] ≤ E_P[w̃] = σ`. -/
theorem spread_le_sigma {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) (hσ : 0 ≤ σ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (μ : Measure ((Fin nP → ℝ) × (ℝ × ℝ × ℝ)))
    (hμ : μ ∈ liftedSpreadSet f θ σ ρ) :
    condMeanGe (μ.map Prod.fst) f θ - condMeanLt (μ.map Prod.fst) f θ ≤
        ρ⁻¹ * ∫ ω, uOf ω ∂μ + (1 - ρ)⁻¹ * ∫ ω, vOf ω ∂μ ∧
      ρ⁻¹ * ∫ ω, uOf ω ∂μ + (1 - ρ)⁻¹ * ∫ ω, vOf ω ∂μ ≤ ∫ ω, wOf ω ∂μ ∧
      ∫ ω, wOf ω ∂μ = σ := by sorry

end DRConvexOpt.Spread
