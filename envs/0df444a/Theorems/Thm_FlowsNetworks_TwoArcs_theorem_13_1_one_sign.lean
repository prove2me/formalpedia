-- Prove2me | Theorems.Thm_FlowsNetworks_TwoArcs_theorem_13_1_one_sign
-- name    : FlowsNetworks.TwoArcs.theorem_13_1_one_sign
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:55.716692+00:00
-- url     : https://prove2.me/theorems/2e59bcde-b093-4ce2-a276-0c692f850fd7
-- title:
--   Chapter I, Theorem 13.1 — the difference quotient qᵢⱼ is of one sign on all rectangles of the nonnegative quadrant
-- statement:
--   Let $[N;\mathcal A]$ be a network with a set $S$ of sources, a disjoint set $T$ of sinks and finite nonnegative arc capacities, and let $A_i\neq A_j$ be two of its arcs. For $\xi,\eta\ge0$ let $\bar v_{ij}(\xi,\eta)$ be the maximal flow value from $S$ to $T$ when the capacities of $A_i$ and $A_j$ are replaced by $\xi$ and $\eta$, and for real $h,k$ with $\xi+h\ge0$, $\eta+k\ge0$ and $hk\neq0$ let
--
--   $$q_{ij}(\xi,\eta;h,k) = \frac{\bar v_{ij}(\xi+h,\eta+k) - \bar v_{ij}(\xi+h,\eta) - \bar v_{ij}(\xi,\eta+k) + \bar v_{ij}(\xi,\eta)}{hk}.$$
--
--   Then $q_{ij}$ is of one sign: either $q_{ij}(\xi,\eta;h,k)\ge0$ for all such $\xi,\eta,h,k$, or $q_{ij}(\xi,\eta;h,k)\le0$ for all of them.
--
--   In words, any two arcs of a network, all other capacities being fixed, either consistently reinforce each other or consistently interfere with each other as their capacities vary. The result is due to Shapley.
--
--   **Formalization Note** The sign is one sign for all rectangles at once (a disjunction of two universal statements), not a sign for each rectangle. Rectangles range over real $\xi,\eta,h,k$ of either sign of $h,k$, with the book's well-definedness conditions $\xi+h\ge0$, $\eta+k\ge0$, $hk\neq0$. The book prints the third term of the numerator as $\bar v_{ij}(\xi,\eta+h)$; the rectangle the theorem names needs $\bar v_{ij}(\xi,\eta+k)$, used here (with the printed term the claim fails on two arcs in series). Several sources and sinks are allowed; if $S$ or $T$ is empty the maximal flow value is identically $0$ and the claim holds trivially.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 57, Theorem 13.1

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network
import Definitions.Def_FlowsNetworks_TwoArcs_TwoArcValue

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

/-- Ch. I, §13, Theorem 13.1, p. 57: for two distinct arcs `A_i, A_j ∈ 𝒜` of a network with
finite nonnegative capacities on the other arcs, the difference quotient `q_ij` of (13.12) is of
one sign over all rectangles in the nonnegative `ξ`–`η` quadrant: either `q_ij ≥ 0` on every
admissible rectangle, or `q_ij ≤ 0` on every admissible rectangle. -/
theorem theorem_13_1_one_sign {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N)
    (hAi : Ai ∈ G.arcs) (hAj : Aj ∈ G.arcs) (hij : Ai ≠ Aj) :
    (∀ ξ η h k : ℝ, IsAdmissible ξ η h k → 0 ≤ diffQuotient G c Ai Aj ξ η h k) ∨
      (∀ ξ η h k : ℝ, IsAdmissible ξ η h k → diffQuotient G c Ai Aj ξ η h k ≤ 0) := by sorry

end FlowsNetworks.TwoArcs
