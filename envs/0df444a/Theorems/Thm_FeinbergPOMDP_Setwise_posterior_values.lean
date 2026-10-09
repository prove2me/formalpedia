-- Prove2me | Theorems.Thm_FeinbergPOMDP_Setwise_posterior_values
-- name    : FeinbergPOMDP.Setwise.posterior_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:34.077544+00:00
-- url     : https://prove2.me/theorems/f3232aa5-09ed-4cb8-8b78-44969a3cb775
-- title:
--   Example 4.1 — posterior values under action $1/n$
-- statement:
--   Fix the belief $z=(1/2,1/2)$, a positive integer $n$, and any filter $H$ satisfying the conditional-law identity (3.3) for the example's state transition $P$ and observation kernel $Q$. For $R'(\cdot\mid z,1/n)$-almost every observation $y$,
--
--   $$
--   f^{(n)}(y)=2\ \Longrightarrow\ H(z,1/n,y)=(1/3,2/3),\qquad
--   f^{(n)}(y)=0\ \Longrightarrow\ H(z,1/n,y)=(1,0).
--   $$
--
--   These are the two posterior points that determine the belief transition under positive-index actions.
--
--   **Formalization Note** The almost-everywhere qualifier is essential: a conditional distribution may be changed arbitrarily on an observation-null set without changing (3.3).
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Example 4.1, p. 14, Bayes's formula paragraph

import Mathlib
import Definitions.Def_FeinbergPOMDP_Setwise_Model

namespace FeinbergPOMDP.Setwise

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Feinberg–Kasyanov–Zgurovsky, arXiv:1401.2168v2, Example 4.1,
p. 14 (Bayes-formula assertion): under action `1/n`, the posterior is
`(1/3,2/3)` on the density-2 event and `(1,0)` on the density-0 event.
The conclusion is almost everywhere because the filter is only determined
almost surely under the observation marginal. -/
theorem posterior_values :
    ∀ H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State,
      IsFilter transition observationKernel H →
      ∀ n : PositiveNat,
        ∀ᵐ y ∂(Rprime transition observationKernel prior (reciprocalAction n)),
          (density n y = 2 → H prior (reciprocalAction n) y = posteriorHigh) ∧
          (density n y = 0 → H prior (reciprocalAction n) y = posteriorLow) := by sorry

end FeinbergPOMDP.Setwise
