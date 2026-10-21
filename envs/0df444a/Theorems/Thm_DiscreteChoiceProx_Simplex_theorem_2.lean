-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_theorem_2
-- name    : DiscreteChoiceProx.Simplex.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:53.986968+00:00
-- url     : https://prove2.me/theorems/07ba2238-09a5-4250-bf55-df8af76f36cd
-- title:
--   Theorem 2 — explicit ℓ₁ convexity parameter
-- statement:
--   Let $\mu$ satisfy Assumption 1. For each ordered pair $i\ne j$, let $g_{ij}$ be a nonnegative measurable density of $\epsilon_j-\epsilon_i$, and let $\bar z_{ij}$ maximize that density. The conjugate $E^*$ is finite on the simplex $\Delta$ and strongly convex there in $\ell_1$ with the paper's parameter
--
--   $$
--   \beta=\frac{1}{2\sum_{i=1}^n\sum_{j\ne i}g_{ij}(\bar z_{ij})}.
--   $$
--
--   Thus the Definition 2 inequality holds for every $p,q\in\Delta$ and $\alpha\in[0,1]$. For $n\ge2$, the displayed parameter is positive. This is the quantitative convexity clause of the prox-function result.
--
--   **Formalization Note** The statement adds `ContDiff ℝ 2 E`: page 7 uses twice differentiability without deriving it from Assumption 1. For $n=1$ the simplex is a point and Lean's reciprocal of the empty denominator is zero. Density versions are tied to the pushforward laws, and the sum counts ordered pairs.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 11, Theorem 2

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- Theorem 2, p. 11: the explicit strong-convexity parameter. -/
theorem theorem_2 {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ)
    (hE : ContDiff ℝ 2 (surplus μ))
    (g : Fin n → Fin n → ℝ → ℝ)
    (hg : ∀ i j, i ≠ j → IsDiffDensity μ i j (g i j))
    (zbar : Fin n → Fin n → ℝ)
    (hmode : ∀ i j, i ≠ j → ∀ z, g i j z ≤ g i j (zbar i j)) :
    (∀ p ∈ simplex n, conj μ p ≠ ⊤) ∧
      IsStronglyConvexL1 (fun p => (conj μ p).toReal) (beta g zbar) ∧
      (2 ≤ n → 0 < beta g zbar) := by sorry

end DiscreteChoiceProx.Simplex
