-- Prove2me | Theorems.Thm_ArapostathisAC_RossReduction_theorem_5_1
-- name    : ArapostathisAC.RossReduction.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:07:41.507873+00:00
-- url     : https://prove2.me/theorems/dea035e1-fd5e-4abd-b252-57ba7340cfcb
-- title:
--   Theorem 5.1: an average cost equation solution verifies optimality
-- statement:
--   Suppose $(\rho,h)$ solves the average cost optimality equation and, for every admissible policy $\pi$ and initial state $i$, the expectations of $h(X_t)$ exist and satisfy
--
--   $$\lim_{t\to\infty}\frac{1}{t}\,E_i^\pi[h(X_t)]=0.$$
--
--   Then $\rho\ge0$, there is a stationary deterministic policy attaining the optimal average cost, and $J^*(i)=\rho$ for every $i$. Any admissible stationary deterministic policy that selects an action attaining the equation's minimum at every state is average-cost optimal.
--
--   This is the verification theorem used to turn the discounted policy in Theorem 5.6 into an average-cost optimal policy.
--
--   **Formalization Note** The printed (5.2) quantifies only over stationary deterministic policies, but the proof applies it to arbitrary admissible policies to establish the infimum over all policies. This item states the condition for all admissible policies. Integrability is explicit so an undefined expectation cannot take Lean's default value zero. The converse clause of Theorem 5.1, which requires irreducibility and positive recurrence, is outside this item.
-- source:
--   Arapostathis et al., Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 299–300, Theorem 5.1, sufficiency and existence clauses; https://doi.org/10.1137/0331018

import Mathlib
import Definitions.Def_ArapostathisAC_RossReduction_CMP

open MeasureTheory Filter Topology

namespace ArapostathisAC.RossReduction

/-- The sufficiency and existence assertions of Theorem 5.1, using (5.2)
for every admissible policy, as required by its proof. -/
theorem theorem_5_1 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hacoe : ACOE M ρ h)
    (hint : ∀ (π : Policy M) (i t : ℕ),
      Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i))
    (hvanish : ∀ (π : Policy M) (i : ℕ),
      Tendsto (fun t : ℕ =>
        (∫ ω, h (ω t).1 ∂(pathMeasure M π i)) / (t : ℝ)) atTop (𝓝 0)) :
    0 ≤ ρ ∧
    (∃ f : ℕ → A, AverageOptimalFor M f ∧
      ∀ i, optAvg M i = ENNReal.ofReal ρ) ∧
    (∀ f : ℕ → A, (∀ i, f i ∈ M.U i) →
      (∀ i, ρ + h i = M.c i (f i) + ∑' j, prob M i (f i) j * h j) →
      AverageOptimalFor M f) := by sorry

end ArapostathisAC.RossReduction
