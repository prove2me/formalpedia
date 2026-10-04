-- Prove2me | Theorems.Thm_DermanSeqDecisions_Stationary_total_cost_abel_limit
-- name    : DermanSeqDecisions.Stationary.total_cost_abel_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:12:24.054095+00:00
-- url     : https://prove2.me/theorems/9d53c608-1da7-43d2-ba66-65601cf0d07b
-- title:
--   $S_R(i) = \lim_{\alpha \to 1^-} V_R(i, \alpha)$, finite or not
-- statement:
--   Let the states and the decisions be finite sets, every decision being available in every state, with transition probabilities $q_{ij}(k)$ and costs $w_{ik} \ge 0$. For a procedure $R \in C$ (history-dependent and randomized) and an initial state $i$, let $W_t$ be the expected cost at time $t$, $V_R(i, \alpha) = \sum_{t \ge 0} \alpha^t W_t$ the discounted cost and $S_R(i) = \sum_{t \ge 0} W_t \in [0, \infty]$ the total cost. Then
--   $$S_R(i) = \lim_{\alpha \to 1^-} V_R(i, \alpha),$$
--   the limit being taken in $[0, \infty]$, so that it holds whether or not $S_R(i)$ is finite.
--
--   In Derman's proof of Theorem 1 (2) this identity, applied along a sequence $\alpha_v \to 1$, turns the discounted optimality of a single stationary procedure into optimality for the total cost.
--
--   **Formalization Note** $S_R(i)$ is `totalCost θ i` and $V_R(i, \alpha)$ is `discCost θ α i`. The limit is along $\alpha \to 1$ with $\alpha < 1$, which includes every sequence $\alpha_v \to 1$ with $\alpha_v < 1$. The only property of the costs used is $w_{ik} \ge 0$, built into the model; the page invokes "$w_{ik} > 0$" at this point.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 19, §2, proof of Theorem 1 (first two lines of the display proving (2))

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria
import Definitions.Def_DermanSeqDecisions_Stationary_totalCost

open scoped ENNReal NNReal Topology
open SennottDP.AvgFinite Filter

namespace DermanSeqDecisions.Stationary

/-- The expected total cost is the Abel limit of the discounted costs (Derman, *On Sequential
Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16,
§2, proof of Theorem 1, p. 19, first two lines of the last display). States `S` and decisions
`Act` are finite, every decision is available in every state, and the costs are nonnegative. For
every procedure `R ∈ C` and initial state `i`,
`S_R(i) = ∑_{t=0}^∞ W_t = lim_{α → 1⁻} V_R(i, α)`, whether or not `S_R(i)` is finite.

**Formalization Note.** `S_R(i)` is `totalCost θ i` and `V_R(i, α)` is `discCost θ α i`, both in
`[0, ∞]`. The limit is taken along the filter `𝓝[<] 1` of `α → 1` from below, which contains every
sequence `α_v → 1` with `α_v < 1` used on the page. The convergence in `[0, ∞]` covers the case
`S_R(i) = ∞`. -/
theorem total_cost_abel_limit {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) :
    Tendsto (fun α : ℝ => discCost θ α i) (𝓝[<] 1) (𝓝 (totalCost θ i)) := by sorry

end DermanSeqDecisions.Stationary
