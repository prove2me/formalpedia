-- Prove2me | Theorems.Thm_FlowsNetworks_TwoArcs_eq_13_4_two_arcs
-- name    : FlowsNetworks.TwoArcs.eq_13_4_two_arcs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:55.325151+00:00
-- url     : https://prove2.me/theorems/b60f7d42-7308-4f6f-95b7-986286f040c6
-- title:
--   Chapter I, Eq. (13.4) — v̄ᵢⱼ(ξ, η) as the minimum of four affine pieces
-- statement:
--   Let $[N;\mathcal A]$ be a network with sources $S$, sinks $T$ and finite nonnegative arc capacities, and let $A_i\neq A_j$ be two arcs. For $\xi,\eta\in[0,\infty]$ let $\bar v_{ij}(\xi,\eta)$ be the maximal flow value from $S$ to $T$ when the capacities of $A_i$ and $A_j$ are replaced by $\xi$ and $\eta$. Then for all $\xi,\eta\in[0,\infty]$
--
--   $$\bar v_{ij}(\xi,\eta) = \min\bigl[\bar v_{ij}(0,0)+\xi+\eta,\ \bar v_{ij}(0,\infty)+\xi,\ \bar v_{ij}(\infty,0)+\eta,\ \bar v_{ij}(\infty,\infty)\bigr].$$
--
--   The maximal flow value is thus a piecewise linear function of the two capacities, determined by its four values at the corners $0$ and $\infty$; this description is what the sign results of the section are read from.
--
--   **Formalization Note** $\xi$, $\eta$ and the values lie in `ℝ≥0∞`; corner values may be $\infty$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 53, Eq. (13.4)

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network
import Definitions.Def_FlowsNetworks_TwoArcs_TwoArcValue

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

/-- Ch. I, §13, Eq. (13.4), p. 53: for two distinct arcs `A_i, A_j ∈ 𝒜`, all other capacities
finite, and `ξ, η ∈ [0, ∞]`,
`v̄_ij(ξ, η) = min[v̄_ij(0, 0) + ξ + η, v̄_ij(0, ∞) + ξ, v̄_ij(∞, 0) + η, v̄_ij(∞, ∞)]`. -/
theorem eq_13_4_two_arcs {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) (ξ η : ℝ≥0∞) :
    vbarTwo G c Ai Aj ξ η =
      min (min (min (vbarTwo G c Ai Aj 0 0 + ξ + η) (vbarTwo G c Ai Aj 0 ⊤ + ξ))
        (vbarTwo G c Ai Aj ⊤ 0 + η)) (vbarTwo G c Ai Aj ⊤ ⊤) := by sorry

end FlowsNetworks.TwoArcs
