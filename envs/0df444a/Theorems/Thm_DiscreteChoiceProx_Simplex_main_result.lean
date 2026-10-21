-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_main_result
-- name    : DiscreteChoiceProx.Simplex.main_result
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:18.560422+00:00
-- url     : https://prove2.me/theorems/6d320090-159e-4a4c-afff-7bd7832c21f0
-- title:
--   Section 2 main result — the surplus conjugate is a prox-function
-- statement:
--   Let $E$ be the surplus of an additive random utility model satisfying Assumption 1. Let $E^*$ be its unrestricted convex conjugate. For ordered pairs $i\ne j$, fix density versions $g_{ij}$ of $\epsilon_j-\epsilon_i$ and modes $\bar z_{ij}$. Then $E^*$ is a prox-function on the simplex $\Delta$: its domain is exactly $\Delta$, it is continuous there, it is strongly convex in $\ell_1$ with
--
--   $$
--   \beta=\frac{1}{2\sum_i\sum_{j\ne i}g_{ij}(\bar z_{ij})},
--   $$
--
--   and for every utility vector $u$ the unique maximizer of $\langle p,u\rangle-E^*(p)$ over $\Delta$ is the choice-probability vector $P(u)$, with attained value $E(u)$. The displayed $\beta$ is positive for $n\ge2$. The goal also asserts the existence of a positive strong-convexity parameter for every $n\ge1$, as Definition 1 requires; at $n=1$ the simplex is a point and the displayed formula evaluates to zero.
--
--   This is the conjunction of the paper's Theorems 1, 2 and 4 and constitutes its Section 2 main result.
--
--   **Formalization Note** The statement adds `ContDiff ℝ 2 E`, following page 7's unproved use of twice differentiability. Assumption 1 includes finite coordinate means, absolute continuity and full support. $E^*$ is `EReal` valued and is converted to real only on its finite domain.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 3, main result; p. 5, Theorem 1; p. 11, Theorem 2; p. 21, Theorem 4

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- The section 2 result, p. 3: `E*` is a prox-function on the simplex. -/
theorem main_result {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ)
    (hE : ContDiff ℝ 2 (surplus μ))
    (g : Fin n → Fin n → ℝ → ℝ)
    (hg : ∀ i j, i ≠ j → IsDiffDensity μ i j (g i j))
    (zbar : Fin n → Fin n → ℝ)
    (hmode : ∀ i j, i ≠ j → ∀ z, g i j z ≤ g i j (zbar i j)) :
    {p | conj μ p ≠ ⊤} = simplex n ∧
    ContinuousOn (fun p => (conj μ p).toReal) (simplex n) ∧
    IsStronglyConvexL1 (fun p => (conj μ p).toReal) (beta g zbar) ∧
    (2 ≤ n → 0 < beta g zbar) ∧
    (∃ β₀ : ℝ, 0 < β₀ ∧
      IsStronglyConvexL1 (fun p => (conj μ p).toReal) β₀) ∧
    (∀ u : Fin n → ℝ,
      choiceProb μ u ∈ simplex n ∧
      (∀ p ∈ simplex n, p ≠ choiceProb μ u →
        pair p u - (conj μ p).toReal <
          pair (choiceProb μ u) u - (conj μ (choiceProb μ u)).toReal) ∧
      pair (choiceProb μ u) u - (conj μ (choiceProb μ u)).toReal = surplus μ u) := by sorry

end DiscreteChoiceProx.Simplex
