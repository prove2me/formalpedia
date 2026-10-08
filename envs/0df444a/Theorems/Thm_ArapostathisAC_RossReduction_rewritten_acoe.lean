-- Prove2me | Theorems.Thm_ArapostathisAC_RossReduction_rewritten_acoe
-- name    : ArapostathisAC.RossReduction.rewritten_acoe
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:07:44.75932+00:00
-- url     : https://prove2.me/theorems/1c390f92-b1d2-43b5-bace-b90af85a9238
-- title:
--   The transformed discounted value solves the original average cost equation
-- statement:
--   Let $\widetilde M$ have the same admissible actions and bounded nonnegative costs as $M$, and let its transition law be the transformation in Theorem 5.6 for $0<\alpha<1$. Write $\widetilde J^*_{1-\alpha}$ for its discounted value. Every value $\widetilde J^*_{1-\alpha}(i)$ is finite, and the value function is bounded. Moreover, with $h(i)=\widetilde J^*_{1-\alpha}(i)$ and $\rho=\alpha\widetilde J^*_{1-\alpha}(0)$,
--
--   $$\rho+h(i)=\min_{a\in U(i)}\left\{c(i,a)+\sum_{j\in S}P(j\mid i,a)h(j)\right\}\qquad(i\in S).$$
--
--   This is the equation at the center of the reduction from average cost for $M$ to discounting for $\widetilde M$.
--
--   **Formalization Note** The minimum is attained, and the real expectation series is summable. The explicit finiteness conclusion prevents conversion of an infinite discounted value to Lean's default real value zero. The cost bound comes from §5.1.
-- source:
--   Arapostathis et al., Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 304, displayed ACOE in proof of Theorem 5.6; https://doi.org/10.1137/0331018

import Mathlib
import Definitions.Def_ArapostathisAC_RossReduction_CMP

namespace ArapostathisAC.RossReduction

/-- The discounted optimality equation for the transformed process,
rewritten as the original process's average cost optimality equation. -/
theorem rewritten_acoe {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M M' : CMP A) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0)
    (hmod : ModifiedLaw M M' α)
    (C : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C) :
    (∀ i, discValue M' (1 - α) i ≠ ⊤) ∧
    (∃ B : ℝ, ∀ i, |(discValue M' (1 - α) i).toReal| ≤ B) ∧
    ACOE M (α * (discValue M' (1 - α) 0).toReal)
      (fun i => (discValue M' (1 - α) i).toReal) := by sorry

end ArapostathisAC.RossReduction
