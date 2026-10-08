-- Prove2me | Theorems.Thm_DemandSubstitution_Correlation_muller_scarsini_normal_sm
-- name    : DemandSubstitution.Correlation.muller_scarsini_normal_sm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:31.596491+00:00
-- url     : https://prove2.me/theorems/80cd575e-1557-4445-9d6c-a1b1ccca14db
-- title:
--   Müller–Scarsini, quoted in the proof of Proposition 2, p. 7 — N(μ, Σ¹) ≤_sm N(μ, Σ²) when σ¹_ii = σ²_ii and σ¹_ij ≤ σ²_ij
-- statement:
--   Let $m\in\mathbb R^n$ and let $\Sigma^1,\Sigma^2$ be positive semidefinite $n\times n$ covariance matrices with equal variances and entrywise ordered covariances:
--   $$\sigma^1_{ii} = \sigma^2_{ii}\ \ \text{for all } i,\qquad \sigma^1_{ij}\le\sigma^2_{ij}\ \ \text{for all } i,j .$$
--   Let $D^1\sim N(m,\Sigma^1)$ and $D^2\sim N(m,\Sigma^2)$. Then $D^1$ is smaller than $D^2$ in the **supermodular order**, $D^1\le_{sm} D^2$: for every supermodular function $f:\mathbb R^n\to\mathbb R$ whose expectations under both laws exist,
--   $$\mathbb E f(D^1) \le \mathbb E f(D^2).$$
--
--   This is the result of Müller and Scarsini quoted in the proof of Proposition 2; it converts an ordering of covariance matrices into an ordering of expectations of supermodular functions, and is the probabilistic core of the mission.
--
--   **Formalization Note.** The supermodular order is the platform's `SupermodularOrder` on laws on `Fin n → ℝ`: the inequality is required for every supermodular $f$ that is integrable under both laws, which is the paper's "for all supermodular functions $f$ such that the expectation exists". The normal laws are Mathlib's `multivariateGaussian` pushed to `Fin n → ℝ`; both matrices are assumed positive semidefinite, since Mathlib's construction degenerates otherwise.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 7, proof of Proposition 2 (result of Müller and Scarsini [12])

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_StochasticOrders_PositiveDependence_Orders
import Definitions.Def_DemandSubstitution_Correlation_Setting

namespace DemandSubstitution.Correlation

open StochasticOrders.PositiveDependence

theorem muller_scarsini_normal_sm {n : ℕ} (m : Fin n → ℝ) (S₁ S₂ : Matrix (Fin n) (Fin n) ℝ)
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hdiag : ∀ k, S₁ k k = S₂ k k) (hle : ∀ k l, S₁ k l ≤ S₂ k l) :
    SupermodularOrder (normalLaw m S₁) (normalLaw m S₂) := by sorry

end DemandSubstitution.Correlation
