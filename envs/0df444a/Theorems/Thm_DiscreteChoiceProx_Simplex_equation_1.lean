-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_equation_1
-- name    : DiscreteChoiceProx.Simplex.equation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:46.485054+00:00
-- url     : https://prove2.me/theorems/67e57cf4-b999-4e58-8b67-516b65323130
-- title:
--   Equation (1) — choice probabilities are surplus derivatives
-- statement:
--   For the surplus $E$ under Assumption 1, the paper states that $E$ is convex and differentiable. Its $i$th coordinate derivative equals the probability that alternative $i$ attains maximal perturbed utility:
--
--   $$
--   \frac{\partial E(u)}{\partial u_i}
--   =P_\mu\!\left(u_i+\epsilon_i=\max_k(u_k+\epsilon_k)\right).
--   $$
--
--   This identity connects the optimization potential $E$ with the discrete-choice model's observable choice probabilities. It is the Williams–Daly–Zachary formula used by Theorem 4.
--
--   **Formalization Note** The event includes ties; Assumption 1 makes ties null. The coordinate derivative is a Fréchet derivative evaluated on a coordinate vector.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 4, equation (1) and preceding sentence

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- The convexity, differentiability and choice-probability formula (1), p. 4. -/
theorem equation_1 {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ) :
    ConvexOn ℝ Set.univ (surplus μ) ∧
      Differentiable ℝ (surplus μ) ∧
      ∀ (u : Fin n → ℝ) (i : Fin n), grad (surplus μ) u i = choiceProb μ u i := by sorry

end DiscreteChoiceProx.Simplex
