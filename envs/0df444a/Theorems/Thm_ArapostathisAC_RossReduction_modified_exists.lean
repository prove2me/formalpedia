-- Prove2me | Theorems.Thm_ArapostathisAC_RossReduction_modified_exists
-- name    : ArapostathisAC.RossReduction.modified_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:07:34.340546+00:00
-- url     : https://prove2.me/theorems/3df61e75-bb23-432d-a151-6116a295aa85
-- title:
--   The transformed transition law defines a controlled Markov process
-- statement:
--   Let $M$ be a countable-state controlled Markov process. Suppose $0<\alpha<1$ and $P(0\mid i,a)\ge\alpha$ for every admissible state-action pair. Then there is a controlled Markov process $\widetilde M$ with the same admissible actions and costs as $M$ and with transition law
--
--   $$\widetilde P(j\mid i,a)=\frac{P(j\mid i,a)-\alpha\mathbf 1_{\{j=0\}}}{1-\alpha}.$$
--
--   This establishes that the transition probabilities used in Theorem 5.6's reduction form a genuine stochastic law, while preserving the standing measurability and continuity conditions.
--
--   **Formalization Note** The paper states $\alpha>0$; its displayed transformation divides by $1-\alpha$, so this item explicitly requires $\alpha<1$. The equation is imposed on admissible pairs only, the domain on which the paper defines the process.
-- source:
--   Arapostathis et al., Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 304, first display in proof of Theorem 5.6; https://doi.org/10.1137/0331018

import Mathlib
import Definitions.Def_ArapostathisAC_RossReduction_CMP

namespace ArapostathisAC.RossReduction

/-- The transition law displayed in the proof of Theorem 5.6 defines a CMP
with the original admissible actions and cost. -/
theorem modified_exists {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0) :
    ∃ M' : CMP A, ModifiedLaw M M' α := by sorry

end ArapostathisAC.RossReduction
