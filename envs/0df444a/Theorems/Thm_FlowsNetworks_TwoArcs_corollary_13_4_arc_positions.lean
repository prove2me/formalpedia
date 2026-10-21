-- Prove2me | Theorems.Thm_FlowsNetworks_TwoArcs_corollary_13_4_arc_positions
-- name    : FlowsNetworks.TwoArcs.corollary_13_4_arc_positions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:59.87572+00:00
-- url     : https://prove2.me/theorems/fb0a2f1b-3613-47d4-8dea-6841cee5cc76
-- title:
--   Chapter I, Corollary 13.4 — common terminal node, two sources, or two sinks give qᵢⱼ ≤ 0
-- statement:
--   Let $[N;\mathcal A]$ be a network with sources $S$, disjoint sinks $T$ and finite nonnegative arc capacities, and let $A_i\neq A_j$ be two arcs. Let $q_{ij}$ be the difference quotient of the maximal flow value $\bar v_{ij}(\xi,\eta)$ over admissible rectangles (real $\xi,\eta\ge0$, $\xi+h\ge0$, $\eta+k\ge0$, $hk\neq0$). Then $q_{ij}\le0$ on every admissible rectangle in each of the following cases:
--
--   1. $A_i$ and $A_j$ have the same terminal node;
--   2. the initial nodes of $A_i$ and $A_j$ are both sources;
--   3. the terminal nodes of $A_i$ and $A_j$ are both sinks.
--
--   $$q_{ij}\le 0.$$
--
--   Together with Theorem 13.3, this lists the positions in which two arcs always interfere.
--
--   **Formalization Note** A conjunction of three implications. The difference quotient uses $\bar v_{ij}(\xi,\eta+k)$ in its third term (the book prints $\eta+h$).
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 61, Corollary 13.4

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network
import Definitions.Def_FlowsNetworks_TwoArcs_TwoArcValue

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

/-- Ch. I, §13, Corollary 13.4, p. 61, for two distinct arcs `A_i, A_j` of `𝒜`: if `A_i` and
`A_j` have the same terminal node, then `q_ij ≤ 0`; if the initial nodes of `A_i` and `A_j` are
both sources, then `q_ij ≤ 0`; if the terminal nodes of `A_i` and `A_j` are both sinks, then
`q_ij ≤ 0`. Each sign holds on every admissible rectangle. -/
theorem corollary_13_4_arc_positions {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) :
    (Ai.2 = Aj.2 →
        ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → diffQuotient G c Ai Aj ξ η h k ≤ 0) ∧
      (Ai.1 ∈ G.sources → Aj.1 ∈ G.sources →
        ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → diffQuotient G c Ai Aj ξ η h k ≤ 0) ∧
      (Ai.2 ∈ G.sinks → Aj.2 ∈ G.sinks →
        ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → diffQuotient G c Ai Aj ξ η h k ≤ 0) := by sorry

end FlowsNetworks.TwoArcs
