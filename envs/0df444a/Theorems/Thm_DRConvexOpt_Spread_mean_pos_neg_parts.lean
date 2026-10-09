-- Prove2me | Theorems.Thm_DRConvexOpt_Spread_mean_pos_neg_parts
-- name    : DRConvexOpt.Spread.mean_pos_neg_parts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:45.883267+00:00
-- url     : https://prove2.me/theorems/8368741e-7769-48a6-a0df-ed0161a228d7
-- title:
--   Proof of Proposition 2, p. 41 — E[[fᵀz̃ − θ]⁺] = ρE[fᵀz̃ | fᵀz̃ ≥ θ] − ρθ and E[[θ − fᵀz̃]⁺] = (1 − ρ)E[−fᵀz̃ | fᵀz̃ < θ] + (1 − ρ)θ
-- statement:
--   Let $\mathbb Q$ be a probability distribution on $\mathbb R^P$ under which $f^\top\tilde z$ is integrable and $\mathbb Q[f^\top\tilde z\ge\theta]=\rho$, where $f\in\mathbb R^P$, $\theta\in\mathbb R$ and $\rho\in(0,1)$. Write $[x]^+=\max\{x,0\}$. Then
--
--   $$
--   \mathbb E_{\mathbb Q}\big[[f^\top\tilde z-\theta]^+\big]=\rho\,\mathbb E_{\mathbb Q}[f^\top\tilde z\mid f^\top\tilde z\ge\theta]-\rho\theta,\qquad
--   \mathbb E_{\mathbb Q}\big[[\theta-f^\top\tilde z]^+\big]=(1-\rho)\,\mathbb E_{\mathbb Q}[-f^\top\tilde z\mid f^\top\tilde z<\theta]+(1-\rho)\theta .
--   $$
--
--   These identities compute the means of the auxiliary variables $\tilde u=[f^\top\tilde z-\theta]^+$ and $\tilde v=[\theta-f^\top\tilde z]^+$ used to lift $\mathbb Q$ into $\mathcal P$.
--
--   **Formalization Note** The conditional means are elementary conditional expectations, $\mathbb E_{\mathbb Q}[f^\top\tilde z\mid A]=\mathbb E_{\mathbb Q}[f^\top\tilde z\,\mathbf 1_A]/\mathbb Q[A]$; both events have probability $\rho$ or $1-\rho$, which are positive because $\rho\in(0,1)$, so no division by zero occurs. The page computes these means under the lift $\mathbb P$; since they depend on $\tilde z$ only, they are stated under $\mathbb Q$. The page's $(1-\rho)\mathbb E[-f^\top\tilde z\mid f^\top\tilde z<\theta]$ is written $(1-\rho)\cdot(-\mathbb E[f^\top\tilde z\mid f^\top\tilde z<\theta])$, equal by linearity.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 41, proof of Proposition 2, the displays for E_P[ũ] and E_P[ṽ]

import Mathlib
import Definitions.Def_DRConvexOpt_Spread_Setting

namespace DRConvexOpt.Spread

open MeasureTheory

/-- Proof of Proposition 2, p. 41: if `Q[fᵀz̃ ≥ θ] = ρ ∈ (0, 1)` and `fᵀz̃` is `Q`-integrable, then
`E[[fᵀz̃ − θ]⁺] = ρ E[fᵀz̃ | fᵀz̃ ≥ θ] − ρθ` and
`E[[θ − fᵀz̃]⁺] = (1 − ρ) E[−fᵀz̃ | fᵀz̃ < θ] + (1 − ρ)θ`. -/
theorem mean_pos_neg_parts {nP : ℕ} (f : Fin nP → ℝ) (θ ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ν : Measure (Fin nP → ℝ)) [IsProbabilityMeasure ν] (hint : Integrable (fun z => f ⬝ᵥ z) ν)
    (hprob : ν.real {z | θ ≤ f ⬝ᵥ z} = ρ) :
    ∫ z, max (f ⬝ᵥ z - θ) 0 ∂ν = ρ * condMeanGe ν f θ - ρ * θ ∧
      ∫ z, max (θ - f ⬝ᵥ z) 0 ∂ν = (1 - ρ) * (-condMeanLt ν f θ) + (1 - ρ) * θ := by sorry

end DRConvexOpt.Spread
