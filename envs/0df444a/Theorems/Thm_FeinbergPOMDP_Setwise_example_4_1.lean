-- Prove2me | Theorems.Thm_FeinbergPOMDP_Setwise_example_4_1
-- name    : FeinbergPOMDP.Setwise.example_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:33.730596+00:00
-- url     : https://prove2.me/theorems/d92759ef-edf6-4a22-808e-8766031e612c
-- title:
--   Example 4.1 — setwise observations do not ensure weak belief continuity
-- statement:
--   Take the two-state POMDP of Example 4.1 with state space $X=\{1,2\}$, observations $Y=[0,1]$, actions $A=\{0\}\cup\{1/n:n\ge1\}$, stationary state transition $P$, and the dyadic observation law $Q$. Then $Q$ is a probability kernel, $P$ is continuous in total variation, and $Q$ is setwise continuous. Moreover $1/n\to0$ in $A$. A filter satisfying (3.3) exists, and for **every** such filter $H$ there is a bounded continuous real test function $g$ on the belief space for which
--
--   $$
--   \int g\,dq_H(\cdot\mid z,1/n)\not\longrightarrow
--   \int g\,dq_H(\cdot\mid z,0),\qquad z=(1/2,1/2).
--   $$
--
--   Thus setwise continuity of observations cannot replace total-variation continuity in the weak-continuity conclusions of Theorems 3.6 and 3.7.
--
--   **Formalization Note** `Fin 2` represents the paper's states 1 and 2 by 0 and 1. The existence clause prevents the universal statement over filters from being vacuous. The claim is along the source's specific sequence of actions, and the belief-law integrals use the Borel σ-algebra of the weak topology.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Example 4.1, pp. 13–14

import Mathlib
import Definitions.Def_FeinbergPOMDP_Setwise_Model

namespace FeinbergPOMDP.Setwise

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

/-- Feinberg–Kasyanov–Zgurovsky, arXiv:1401.2168v2, Example 4.1,
pp. 13–14: the identity state transition is total-variation continuous,
the dyadic observation kernel is setwise continuous, but at the uniform
belief the posterior laws along actions `1/n → 0` fail weak convergence.
The filter exists and the failure holds for every version satisfying (3.3). -/
theorem example_4_1 :
    IsMarkovKernel observationKernel ∧
    TVContinuous (fun p : State × Action => transition p) ∧
    SetwiseContinuous (fun p : Action × State => observationKernel p) ∧
    Tendsto (fun k : ℕ => reciprocalAction ⟨k + 1, by omega⟩)
      atTop (𝓝 zeroAction) ∧
    (∃ H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State,
      IsFilter transition observationKernel H) ∧
    ∀ H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State,
      IsFilter transition observationKernel H →
      ∃ g : ProbabilityMeasure State →ᵇ ℝ,
        ¬ Tendsto
          (fun k : ℕ => ∫ b, g b ∂(beliefTransition transition observationKernel H prior
            (reciprocalAction ⟨k + 1, by omega⟩))) atTop
          (𝓝 (∫ b, g b ∂(beliefTransition transition observationKernel H prior zeroAction))) := by sorry

end FeinbergPOMDP.Setwise
