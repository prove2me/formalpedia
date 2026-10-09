-- Prove2me | Theorems.Thm_DRConvexOpt_Spread_mean_combination
-- name    : DRConvexOpt.Spread.mean_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:40:06.34327+00:00
-- url     : https://prove2.me/theorems/6ca67181-511c-4c9c-a452-f4bc7f5552d8
-- title:
--   Proof of Proposition 2, p. 41 — E[ρ⁻¹ũ + (1 − ρ)⁻¹ṽ] equals the absolute mean spread
-- statement:
--   Let $\mathbb Q$ be a probability distribution on $\mathbb R^P$ under which $f^\top\tilde z$ is integrable and $\mathbb Q[f^\top\tilde z\ge\theta]=\rho$, where $f\in\mathbb R^P$, $\theta\in\mathbb R$ and $\rho\in(0,1)$. Write $[x]^+=\max\{x,0\}$. With $\tilde u=[f^\top\tilde z-\theta]^+$ and $\tilde v=[\theta-f^\top\tilde z]^+$,
--
--   $$
--   \mathbb E_{\mathbb Q}\big[\rho^{-1}\tilde u+(1-\rho)^{-1}\tilde v\big]=\mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z\ge\theta]-\mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z<\theta].
--   $$
--
--   So the lift of $\mathbb Q$ satisfies the moment constraint of $\mathcal P$ up to a nonnegative slack, which is what makes $\mathbb Q$ a marginal of a member of $\mathcal P$.
--
--   **Formalization Note** The conditional means are elementary conditional expectations, $\mathbb E_{\mathbb Q}[f^\top\tilde z\mid A]=\mathbb E_{\mathbb Q}[f^\top\tilde z\,\mathbf 1_A]/\mathbb Q[A]$; both events have probability $\rho$ or $1-\rho$, which are positive because $\rho\in(0,1)$, so no division by zero occurs. The expectation is stated under $\mathbb Q$, since the integrand depends on $\tilde z$ only.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 41, proof of Proposition 2, sentence “We thus conclude that …”

import Mathlib
import Definitions.Def_DRConvexOpt_Spread_Setting

namespace DRConvexOpt.Spread

open MeasureTheory

/-- Proof of Proposition 2, p. 41: under the hypotheses of `mean_pos_neg_parts`, with
`ũ = [fᵀz̃ − θ]⁺` and `ṽ = [θ − fᵀz̃]⁺`,
`E[ρ⁻¹ũ + (1 − ρ)⁻¹ṽ] = E[fᵀz̃ | fᵀz̃ ≥ θ] − E[fᵀz̃ | fᵀz̃ < θ]`. -/
theorem mean_combination {nP : ℕ} (f : Fin nP → ℝ) (θ ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ν : Measure (Fin nP → ℝ)) [IsProbabilityMeasure ν] (hint : Integrable (fun z => f ⬝ᵥ z) ν)
    (hprob : ν.real {z | θ ≤ f ⬝ᵥ z} = ρ) :
    ∫ z, (ρ⁻¹ * max (f ⬝ᵥ z - θ) 0 + (1 - ρ)⁻¹ * max (θ - f ⬝ᵥ z) 0) ∂ν =
      condMeanGe ν f θ - condMeanLt ν f θ := by sorry

end DRConvexOpt.Spread
