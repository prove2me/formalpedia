-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_theorem_1
-- name    : DiscreteChoiceProx.Simplex.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:26.853259+00:00
-- url     : https://prove2.me/theorems/533548bc-48aa-4422-ab35-4ce6f3ab9388
-- title:
--   Theorem 1 — domain and continuity of the conjugate
-- statement:
--   Let $E$ be the surplus of a random utility law satisfying Assumption 1, and let $E^*$ be its unrestricted convex conjugate. Its finite domain is precisely the probability simplex $\Delta$, and it is continuous throughout that domain:
--
--   $$
--   \operatorname{dom} E^*=\{p:E^*(p)<+\infty\}=\Delta,
--   \qquad E^*|_\Delta\text{ is continuous}.
--   $$
--
--   Continuity includes the boundary faces of the simplex. This gives the continuity clause of the paper's prox-function result.
--
--   **Formalization Note** $E^*$ is `EReal` valued. The real-valued restriction uses `toReal` only with the domain equality, which supplies finiteness on $\Delta$.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 5, Theorem 1

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- Theorem 1, p. 5: domain and continuity of the conjugate. -/
theorem theorem_1 {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ) :
    {p | conj μ p ≠ ⊤} = simplex n ∧
      ContinuousOn (fun p => (conj μ p).toReal) (simplex n) := by sorry

end DiscreteChoiceProx.Simplex
