-- Prove2me | Theorems.Thm_FeinbergPOMDP_Setwise_observation_setwise
-- name    : FeinbergPOMDP.Setwise.observation_setwise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:34.761372+00:00
-- url     : https://prove2.me/theorems/25638e79-512f-4063-8082-074211ce0d19
-- title:
--   Example 4.1 — observation kernel is setwise continuous
-- statement:
--   On $A=\{0\}\cup\{1/n:n\ge1\}$ and $X=\{1,2\}$, let $Q$ be the observation law of Example 4.1: Lebesgue measure at state 1 and at action zero, and $m^{(n)}$ at state 2 under action $1/n$. Every $Q(\cdot\mid a,x)$ is a probability measure, and for every convergent sequence $(a_j,x_j)\to(a,x)$ and every Borel observation set $C$,
--
--   $$
--   Q(C\mid a_j,x_j)\longrightarrow Q(C\mid a,x).
--   $$
--
--   This confirms that the example meets the setwise-continuity hypothesis whose insufficiency it demonstrates. The limit is taken in the real subspace topology on $A$ and the discrete topology on $X$.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Example 4.1, p. 13, first part

import Mathlib
import Definitions.Def_FeinbergPOMDP_Setwise_Model

namespace FeinbergPOMDP.Setwise

open MeasureTheory ProbabilityTheory

/-- Feinberg–Kasyanov–Zgurovsky, arXiv:1401.2168v2, Example 4.1,
p. 13 (unnumbered assertion): the concrete observation law is a stochastic
kernel and is setwise continuous on the literal action and state spaces. -/
theorem observation_setwise :
    IsMarkovKernel observationKernel ∧
      SetwiseContinuous (fun p : Action × State => observationKernel p) := by sorry

end FeinbergPOMDP.Setwise
