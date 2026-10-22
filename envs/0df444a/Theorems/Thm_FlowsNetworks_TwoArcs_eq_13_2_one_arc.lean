-- Prove2me | Theorems.Thm_FlowsNetworks_TwoArcs_eq_13_2_one_arc
-- name    : FlowsNetworks.TwoArcs.eq_13_2_one_arc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:54.655399+00:00
-- url     : https://prove2.me/theorems/32979ea6-32f5-43c4-8f38-ecaa22018ad7
-- title:
--   Chapter I, Eq. (13.2) — v̄ᵢ(ξ) = min[v̄ᵢ(0) + ξ, v̄ᵢ(∞)]
-- statement:
--   Let $[N;\mathcal A]$ be a network with sources $S$, sinks $T$ and finite nonnegative arc capacities, and let $A_i\in\mathcal A$. For $\xi\in[0,\infty]$ let $\bar v_i(\xi)$ be the maximal flow value from $S$ to $T$ when the capacity of $A_i$ is replaced by $\xi$. Then for every $\xi\in[0,\infty]$
--
--   $$\bar v_i(\xi) = \min\bigl[\bar v_i(0)+\xi,\ \bar v_i(\infty)\bigr].$$
--
--   So the maximal flow value grows with slope one in the capacity of a single arc until it reaches the value it has with that arc uncapacitated, and is constant from then on.
--
--   **Formalization Note** $\xi$ and the values lie in `ℝ≥0∞`; addition with $\infty$ is the usual one, and $\bar v_i(\infty)$ may be $\infty$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 53, Eq. (13.2)

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network
import Definitions.Def_FlowsNetworks_TwoArcs_TwoArcValue

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

/-- Ch. I, §13, Eq. (13.2), p. 53: with all other capacities finite and the capacity of the arc
`A_i ∈ 𝒜` replaced by `ξ ∈ [0, ∞]`, `v̄_i(ξ) = min[v̄_i(0) + ξ, v̄_i(∞)]`. -/
theorem eq_13_2_one_arc {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) (Ai : N × N) (hAi : Ai ∈ G.arcs) (ξ : ℝ≥0∞) :
    vbarOne G c Ai ξ = min (vbarOne G c Ai 0 + ξ) (vbarOne G c Ai ⊤) := by sorry

end FlowsNetworks.TwoArcs
