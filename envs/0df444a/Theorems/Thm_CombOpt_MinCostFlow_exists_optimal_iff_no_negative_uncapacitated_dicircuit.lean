-- Prove2me | Theorems.Thm_CombOpt_MinCostFlow_exists_optimal_iff_no_negative_uncapacitated_dicircuit
-- name    : CombOpt.MinCostFlow.exists_optimal_iff_no_negative_uncapacitated_dicircuit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:47.275956+00:00
-- url     : https://prove2.me/theorems/f481f702-e083-47f2-bb8f-316e49c7dd73
-- title:
--   Theorem 4.4 — an optimum exists iff no negative-cost dicircuit of infinite-capacity arcs
-- statement:
--   Consider the minimum-cost flow problem (4.1) on a digraph $G$ with demands $b$ ($b(V)=0$), nonnegative capacities $u\in(\mathbb R\cup\{\infty\})^E$ and costs $c$. Suppose that (4.1) has a feasible solution. Then it has an optimal solution if and only if there is no dicircuit $C$ of $G$ with $u_e=\infty$ for every arc $e$ of $C$ and
--
--   $$\sum(c_e : e\in C)<0.$$
--
--   The theorem separates the two ways (4.1) can fail to have an optimum: infeasibility, and unboundedness along an uncapacitated negative dicircuit.
--
--   Differences from the source:
--   - encoding: capacities u ∈ (ℝ ∪ {∞})^E, u ≥ 0 → u : E → EReal with 0 ≤ u e, u e = ⊤ for u_e = ∞; reason: Lean convention; the same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 4.4, p. 94 (PDF p. 102)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalFlow
import Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit_cost
import Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit_IsDicircuit

namespace CombOpt.MinCostFlow

/-- **Theorem 4.4 (existence of an optimal solution).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 4.4, p. 94 (PDF p. 102): "Suppose that (4.1) has a feasible solution. Then it has an
optimal solution if and only if there exists no negative-cost dicircuit of G, each of whose arcs
has infinite capacity."

**Formalization Note.** The standing assumptions of §4.1, p. 91 ("u ∈ (ℝ ∪ {∞})^E is nonnegative, and b(V) = 0"), are the hypotheses `hu` and `hb`; capacities are `EReal` with `u e = ⊤` for `u_e = ∞`. A dicircuit is a `G.Circuit` all of whose arcs are forward; its
cost is the sum of `c` over its arcs. -/
theorem exists_optimal_iff_no_negative_uncapacitated_dicircuit {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Digraph V E) (b : V → ℝ) (u : E → EReal) (c : E → ℝ)
    (hb : ∑ v, b v = 0) (hu : ∀ e, 0 ≤ u e)
    (hfeas : ∃ x, G.IsFeasibleFlow b u x) :
    (∃ x, G.IsOptimalFlow b u c x) ↔
      ¬∃ C : G.Circuit, C.IsDicircuit ∧ (∀ i, u (C.arc i) = ⊤) ∧ C.cost c < 0 := by sorry

end CombOpt.MinCostFlow
