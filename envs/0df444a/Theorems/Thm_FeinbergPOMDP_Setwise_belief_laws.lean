-- Prove2me | Theorems.Thm_FeinbergPOMDP_Setwise_belief_laws
-- name    : FeinbergPOMDP.Setwise.belief_laws
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:33.008961+00:00
-- url     : https://prove2.me/theorems/1cb7bf90-10a9-4c1a-b0a1-bde3f6323985
-- title:
--   Example 4.1 — fixed two-point belief law versus action zero
-- statement:
--   Fix $z=(1/2,1/2)$ and any filter $H$ satisfying (3.3) for the example. For every positive integer $n$, the posterior transition under action $1/n$ has the same law, whereas action zero leaves the belief unchanged:
--
--   $$
--   q_H(\cdot\mid z,1/n)=\tfrac34\delta_{(1/3,2/3)}+\tfrac14\delta_{(1,0)},
--   \qquad q_H(\cdot\mid z,0)=\delta_z.
--   $$
--
--   This is the explicit separation of the positive-index and zero-action belief laws. It holds independently of the version of the filter.
--
--   **Formalization Note** The measures on beliefs use the Borel σ-algebra of the weak topology. The paper's phrase “$f^{(n)}(2)=2$ with probability $3/4$” is treated as the event $f^{(n)}(y)=2$; the source wording is preserved in the milestone quotation.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Example 4.1, p. 14, final paragraph

import Mathlib
import Definitions.Def_FeinbergPOMDP_Setwise_Model

namespace FeinbergPOMDP.Setwise

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Feinberg–Kasyanov–Zgurovsky, arXiv:1401.2168v2, Example 4.1,
p. 14 (unnumbered law assertion): every positive-index action has the
same two-point posterior law, while action zero leaves the belief fixed.
This holds for every version of the filter satisfying (3.3). -/
theorem belief_laws :
    ∀ H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State,
      IsFilter transition observationKernel H →
      (∀ n : PositiveNat,
        beliefTransition transition observationKernel H prior (reciprocalAction n) =
          (3 / 4 : ℝ≥0∞) •
            (@Measure.dirac (ProbabilityMeasure State) (borel (ProbabilityMeasure State)) posteriorHigh) +
          (1 / 4 : ℝ≥0∞) •
            (@Measure.dirac (ProbabilityMeasure State) (borel (ProbabilityMeasure State)) posteriorLow)) ∧
      beliefTransition transition observationKernel H prior zeroAction =
        @Measure.dirac (ProbabilityMeasure State) (borel (ProbabilityMeasure State)) prior := by sorry

end FeinbergPOMDP.Setwise
