-- Prove2me | Theorems.Thm_ArapostathisAC_RossReduction_theorem_5_6
-- name    : ArapostathisAC.RossReduction.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:08:04.625902+00:00
-- url     : https://prove2.me/theorems/3f6e8425-7453-42b4-b415-fa4ce6bcf42e
-- title:
--   Theorem 5.6: a common one-step return probability reduces average cost to discounting
-- statement:
--   Let $M$ have bounded nonnegative one-stage costs. Suppose $0<\alpha<1$ and $P(0\mid i,a)\ge\alpha$ for every admissible state-action pair. Then a transformed process $\widetilde M$ exists with the same admissible actions and costs, and transition law
--
--   $$\widetilde P(j\mid i,a)=\frac{P(j\mid i,a)-\alpha\mathbf 1_{\{j=0\}}}{1-\alpha}.$$
--
--   Its $(1-\alpha)$-discounted value is finite in every state, and a stationary deterministic $(1-\alpha)$-discount-optimal policy exists. Every such policy is average-cost optimal for $M$, with the same optimal average cost from every state:
--
--   $$J^*(i)=\alpha\widetilde J^*_{1-\alpha}(0)\qquad(i\in S).$$
--
--   This gives the precise mathematical content of the paper's phrase that the average-cost problem can be reduced to an appropriate discounted-cost problem.
--
--   **Formalization Note** Bounded cost is the standing assumption of §5.1. The paper states $\alpha>0$; the displayed transformed law requires $\alpha<1$. Optimal values are infima over all admissible, possibly randomized, history-dependent policies. The transformed law is tied to the original one on every admissible state-action pair; the conclusion does not assume average optimality of the selected policy.
-- source:
--   Arapostathis et al., Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 303–304, Theorem 5.6 and proof; https://doi.org/10.1137/0331018

import Mathlib
import Definitions.Def_ArapostathisAC_RossReduction_CMP

namespace ArapostathisAC.RossReduction

/-- The precise reduction asserted in the proof of Theorem 5.6. -/
theorem theorem_5_6 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (C : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0) :
    ∃ M' : CMP A, ModifiedLaw M M' α ∧
      (∀ i, discValue M' (1 - α) i ≠ ⊤) ∧
      (∃ f : ℕ → A, DiscountOptimalFor M' (1 - α) f) ∧
      (∀ f : ℕ → A, DiscountOptimalFor M' (1 - α) f →
        AverageOptimalFor M f) ∧
      (∀ i, optAvg M i =
        ENNReal.ofReal (α * (discValue M' (1 - α) 0).toReal)) := by sorry

end ArapostathisAC.RossReduction
