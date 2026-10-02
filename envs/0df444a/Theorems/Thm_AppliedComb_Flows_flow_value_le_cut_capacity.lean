-- Prove2me | Theorems.Thm_AppliedComb_Flows_flow_value_le_cut_capacity
-- name    : AppliedComb.Flows.flow_value_le_cut_capacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:39:22.383526+00:00
-- url     : https://prove2.me/theorems/e81308d1-cc5f-4bef-9ce3-70cd45ce4a5e
-- title:
--   Theorem 13.4 — the value of a flow is at most the capacity of a cut
-- statement:
--   Let $G = (V, E)$ be a network with source $S$, sink $T$ and capacities $c$, let $\phi$ be a flow in $G$, and let $V = L \cup U$ be a cut ($S \in L$, $T \in U$). Then the value of the flow is at most as large as the capacity of the cut:
--   $$\sum_{x \in V} \phi(S, x) \;\le\; c(L, U) = \sum_{x \in L,\ y \in U} c(x, y).$$
--
--   This is the easy half of the Max Flow–Min Cut Theorem: every cut is an upper bound for every flow value, so a flow and a cut with equal value and capacity certify each other's optimality.
--
--   **Formalization Note.** Networks, flows, values, cuts and cut capacities are those of `AppliedComb.Flows.Network`; the cut is given by its part `L` containing the source and not the sink.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 262, Theorem 13.4

import Mathlib
import Definitions.Def_AppliedComb_Flows_Network

namespace AppliedComb.Flows

/-- **Theorem 13.4** (Keller & Trotter, *Applied Combinatorics*, 2017 Edition, p. 262). Let `N`
be a network, let `ϕ` be a flow in `N`, and let `V = L ∪ U` be a cut. The value of the flow is
at most as large as the capacity of the cut. -/
theorem flow_value_le_cut_capacity {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ϕ : V → V → ℝ) (hϕ : N.IsFlow ϕ) (L : Finset V) (hL : N.IsCut L) :
    N.value ϕ ≤ N.cutCapacity L := by sorry

end AppliedComb.Flows
