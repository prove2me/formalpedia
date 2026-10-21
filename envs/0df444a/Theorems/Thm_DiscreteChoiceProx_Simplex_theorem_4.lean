-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_theorem_4
-- name    : DiscreteChoiceProx.Simplex.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:05.588182+00:00
-- url     : https://prove2.me/theorems/c46a579d-5322-4dba-994f-64f704b031ff
-- title:
--   Theorem 4 — choice probabilities solve the prox step
-- statement:
--   For any utility vector $u$, maximize $\langle p,u\rangle-E^*(p)$ over the probability simplex $\Delta$. Under Assumption 1 and the strong-convexity premise stated at the start of §2.2.3, the unique maximizer is the vector of choice probabilities, and the optimal value is the surplus:
--
--   $$
--   \underset{p\in\Delta}{\operatorname{argmax}}
--   \bigl(\langle p,u\rangle-E^*(p)\bigr)=P(u),\qquad
--   \max_{p\in\Delta}\bigl(\langle p,u\rangle-E^*(p)\bigr)=E(u).
--   $$
--
--   Each component $P_i(u)$ is the probability that alternative $i$ attains the largest perturbed utility. The theorem supplies the explicit optimization step demanded by Definition 1's simplicity clause.
--
--   **Formalization Note** The conjugate is read as a real number only for points of $\Delta$, where Theorem 1 makes it finite. The positive strong-convexity parameter is an explicit premise because the paper assumes it in the opening of §2.2.3.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 21, Theorem 4 and equation (4)

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- Theorem 4, p. 21: the choice vector is the unique maximizer in (4). -/
theorem theorem_4 {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ)
    (hStrong : ∃ β : ℝ, 0 < β ∧
      IsStronglyConvexL1 (fun p => (conj μ p).toReal) β) :
    ∀ u : Fin n → ℝ,
      choiceProb μ u ∈ simplex n ∧
      (∀ p ∈ simplex n, p ≠ choiceProb μ u →
        pair p u - (conj μ p).toReal <
          pair (choiceProb μ u) u - (conj μ (choiceProb μ u)).toReal) ∧
      pair (choiceProb μ u) u - (conj μ (choiceProb μ u)).toReal = surplus μ u := by sorry

end DiscreteChoiceProx.Simplex
