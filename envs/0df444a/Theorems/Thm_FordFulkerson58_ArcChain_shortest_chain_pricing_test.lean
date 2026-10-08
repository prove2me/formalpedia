-- Prove2me | Theorems.Thm_FordFulkerson58_ArcChain_shortest_chain_pricing_test
-- name    : FordFulkerson58.ArcChain.shortest_chain_pricing_test
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:38:53.180323+00:00
-- url     : https://prove2.me/theorems/aa9b5ed6-1a34-41cc-bcae-eba499230b0c
-- title:
--   §3, pp. 1779–1780 — with α ≥ 0, the labeling process terminates; sink labels ≥ 1 ⇒ the basis is optimal; a sink label < 1 ⇒ an entering chain
-- statement:
--   Consider the arc-chain program (2)–(3) of a multi-commodity network with arcs $A_1,\dots,A_m$. Let $B$ be a basis (columns $s_1,\dots,s_m$ of $[A\mid I]$ with invertible submatrix), $z$ its basic feasible solution, and $\alpha_1,\dots,\alpha_m$ its simplex multipliers, i.e. the solution of (4). Assume all $\alpha_r \ge 0$, and run the labeling process of §3 for each commodity $k$ with arc lengths $\alpha_r$, starting from $\pi_i = 0$ on the sources $S_k$ and $\pi_i = \infty$ elsewhere. Then:
--
--   1. **(termination)** for every commodity, every run of the labeling process is finite;
--   2. **(optimality)** if, for every commodity $k$, the final labels $\pi^{(k)}$ satisfy $\pi^{(k)}_t \ge 1$ at every sink $t \in T_k$, then the basis is optimal: every feasible solution of (3) has
--   $$\sum_{s=1}^{n} x_s \le \sum_{s=1}^{n} z_s;$$
--   3. **(entering chain)** if, for some commodity $k$, the final labels satisfy $\pi_t < 1$ at some sink $t \in T_k$, then there is a commodity chain $C_s$ of $k$ from $S_k$ to $t$ whose length $\sum_r \alpha_r a_{rs}$ equals $\pi_t$, whose column is not in the basis, and whose reduced cost is positive:
--   $$1 - \sum_{r=1}^{m} \alpha_r a_{rs} > 0,$$
--   so the column of $A$ corresponding to this chain may be introduced into the basis.
--
--   This is the paper's main proposal: the pricing step of the simplex method on the arc-chain program, which would otherwise require the whole incidence matrix $A$, is carried out by one shortest chain computation per commodity.
--
--   **Formalization Note** "Final labels" means a labeling reachable from the initial labels by steps of the process and admitting no further step; part 1 shows such labelings exist, so parts 2 and 3 are not vacuous. Part 3 claims a positive reduced cost and non-basicness only; the page claims no strict increase of (2), which can fail under degeneracy. Labels are in `WithTop ℝ`; a sink with label $\infty$ (no chain) counts as $\ge 1$.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), pp. 1779–1780, §3 (the pricing test on p. 1779 and the labeling process on p. 1780)

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_LP
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, pp. 1779–1780, the shortest-chain pricing test. Let `β` be a feasible basis of the arc-chain
program (2)–(3) with basic solution `z` and simplex multipliers `α` (4), all `α_r ≥ 0`, and use the
`α_r` as arc lengths. Then
(a) for every commodity, the labeling process from the commodity's sources terminates;
(b) if for every commodity the final labels at all its sinks are at least `1`, the basis is optimal;
(c) if for some commodity the final label of a sink `t` is below `1`, there is a chain from the
commodity's sources to `t` of length equal to that label, whose column is not basic and has positive
reduced cost `1 − ∑_r α_r a_rs`, so it may be introduced into the basis. -/
theorem shortest_chain_pricing_test {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (β : E → Col N ⊕ E) (hβ : IsUnit (basisMatrix N β).det)
    (z : Col N ⊕ E → ℝ) (hz : IsBasicFeasibleSolution N β z)
    (α : E → ℝ) (h4 : IsSimplexMultiplier N β α)
    (hα : ∀ r, 0 ≤ α r) :
    (∀ k : ι, ¬ ∃ f : ℕ → V → WithTop ℝ,
        f 0 = initLabel (N.src k) ∧ ∀ i, RelaxStep N α (f i) (f (i + 1))) ∧
    (∀ lab : ι → V → WithTop ℝ,
        (∀ k, Relation.ReflTransGen (RelaxStep N α) (initLabel (N.src k)) (lab k) ∧
          IsTerminal N α (lab k)) →
        (∀ k, ∀ t ∈ N.snk k, (1 : WithTop ℝ) ≤ lab k t) →
        ∀ (x : Col N → ℝ) (y : E → ℝ), Feasible N x y → ∑ s, x s ≤ ∑ s, z (Sum.inl s)) ∧
    (∀ (k : ι) (lab : V → WithTop ℝ),
        Relation.ReflTransGen (RelaxStep N α) (initLabel (N.src k)) lab → IsTerminal N α lab →
        ∀ t ∈ N.snk k, lab t < 1 →
        ∃ (C : Finset E) (h : IsCommodityChain N k C), IsChainFrom N (N.src k) t C ∧
          ((chainLength α C : ℝ) : WithTop ℝ) = lab t ∧
          0 < reducedCost N α (Sum.inl ⟨(k, C), h⟩) ∧
          (Sum.inl ⟨(k, C), h⟩ : Col N ⊕ E) ∉ Set.range β) := by sorry

end FordFulkerson58.ArcChain
