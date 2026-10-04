-- Prove2me | Theorems.Thm_AppliedComb_Flows_max_flow_min_cut
-- name    : AppliedComb.Flows.max_flow_min_cut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:40:35.340623+00:00
-- url     : https://prove2.me/theorems/e42ad658-77f8-4935-92e3-ba6618710855
-- title:
--   Theorem 13.10 — The Max Flow–Min Cut Theorem
-- statement:
--   Let $G = (V, E)$ be a network with source $S$, sink $T$ and non-negative real capacities $c$. Then there is a real number $v_0$ that is both the maximum value of a flow and the minimum capacity of a cut:
--   $$v_0 = \max\{\operatorname{value}(\phi) : \phi \text{ a flow in } G\} = \min\{c(L, U) : V = L \cup U \text{ a cut}\}.$$
--   In words: some flow has value $v_0$ and no flow has larger value; some cut has capacity $v_0$ and no cut has smaller capacity.
--
--   This is the central theorem of network flows, due to Ford and Fulkerson (1956) and to Elias, Feinstein and Shannon (1956). The book obtains it from the Ford–Fulkerson labeling algorithm (Algorithm 13.11): when the labeling halts without labeling the sink, the labeled and unlabeled vertices form a cut whose capacity equals the current flow's value.
--
--   **Formalization Note.** The book's sentence "if $v_0$ is the maximum value of a flow and $c_0$ is the minimum capacity of a cut, then $v_0 = c_0$" presupposes that both extrema exist. The statement here asserts their existence as well as their equality (`IsGreatest` of the set of flow values and `IsLeast` of the set of cut capacities, at the same number), so nothing is assumed. For real (possibly irrational) capacities the labeling algorithm need not terminate, so the existence of a maximum flow is part of the claim.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 268, Theorem 13.10

import Mathlib
import Definitions.Def_AppliedComb_Flows_Network

namespace AppliedComb.Flows

/-- **Theorem 13.10 (The Max Flow–Min Cut Theorem)** (Keller & Trotter, *Applied Combinatorics*,
2017 Edition, p. 268). Let `N` be a network. There is a number `v₀` which is the maximum value
of a flow in `N` (it is the value of some flow, and no flow has larger value) and which is also
the minimum capacity of a cut of `N` (it is the capacity of some cut, and no cut has smaller
capacity). In particular the maximum value of a flow exists, the minimum capacity of a cut exists,
and they are equal. -/
theorem max_flow_min_cut {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) :
    ∃ v₀ : ℝ,
      IsGreatest {v : ℝ | ∃ ϕ : V → V → ℝ, N.IsFlow ϕ ∧ N.value ϕ = v} v₀ ∧
      IsLeast {c : ℝ | ∃ L : Finset V, N.IsCut L ∧ N.cutCapacity L = c} v₀ := by sorry

end AppliedComb.Flows
