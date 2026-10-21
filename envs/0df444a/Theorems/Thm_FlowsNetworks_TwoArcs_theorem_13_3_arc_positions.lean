-- Prove2me | Theorems.Thm_FlowsNetworks_TwoArcs_theorem_13_3_arc_positions
-- name    : FlowsNetworks.TwoArcs.theorem_13_3_arc_positions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:55.846237+00:00
-- url     : https://prove2.me/theorems/1a8e984d-90f8-460c-aeb9-dd7d347b33f3
-- title:
--   Chapter I, Theorem 13.3 — the sign of qᵢⱼ from the relative positions of Aᵢ and Aⱼ
-- statement:
--   Let $[N;\mathcal A]$ be a network with sources $S$, disjoint sinks $T$ and finite nonnegative arc capacities, and let $A_i\neq A_j$ be two arcs; an arc $(x,y)$ has initial node $x$ and terminal node $y$. Let $q_{ij}$ be the difference quotient of the maximal flow value $\bar v_{ij}(\xi,\eta)$ over admissible rectangles (real $\xi,\eta\ge0$, $\xi+h\ge0$, $\eta+k\ge0$, $hk\neq0$). Then
--
--   1. if the terminal node of $A_i$ is the initial node of $A_j$, then $q_{ij}\ge0$ on every admissible rectangle;
--   2. if $A_i$ and $A_j$ have the same initial node, then $q_{ij}\le0$ on every admissible rectangle;
--   3. if the initial node of $A_i$ is a source and the terminal node of $A_j$ is a sink, then $q_{ij}\ge0$ on every admissible rectangle.
--
--   $$\text{(i), (iii)}:\ q_{ij}\ge 0,\qquad \text{(ii)}:\ q_{ij}\le0.$$
--
--   These are cases where the interaction type of two arcs is fixed by their positions alone, whatever the other capacities are.
--
--   **Formalization Note** The three parts are a conjunction of three implications. The difference quotient uses $\bar v_{ij}(\xi,\eta+k)$ in its third term (the book prints $\eta+h$).
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 59, Theorem 13.3

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network
import Definitions.Def_FlowsNetworks_TwoArcs_TwoArcValue

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

/-- Ch. I, §13, Theorem 13.3, p. 59, for two distinct arcs `A_i = (x_i, y_i)`,
`A_j = (x_j, y_j)` of `𝒜` (initial node first, terminal node second):
(i) if the terminal node of `A_i` is the initial node of `A_j`, then `q_ij ≥ 0`;
(ii) if `A_i` and `A_j` have the same initial node, then `q_ij ≤ 0`;
(iii) if the initial node of `A_i` is a source and the terminal node of `A_j` is a sink, then
`q_ij ≥ 0`. Each sign holds on every admissible rectangle. -/
theorem theorem_13_3_arc_positions {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) :
    (Ai.2 = Aj.1 →
        ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → 0 ≤ diffQuotient G c Ai Aj ξ η h k) ∧
      (Ai.1 = Aj.1 →
        ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → diffQuotient G c Ai Aj ξ η h k ≤ 0) ∧
      (Ai.1 ∈ G.sources → Aj.2 ∈ G.sinks →
        ∀ ξ η h k : ℝ, IsAdmissible ξ η h k → 0 ≤ diffQuotient G c Ai Aj ξ η h k) := by sorry

end FlowsNetworks.TwoArcs
