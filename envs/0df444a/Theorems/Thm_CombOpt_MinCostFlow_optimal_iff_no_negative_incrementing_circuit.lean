-- Prove2me | Theorems.Thm_CombOpt_MinCostFlow_optimal_iff_no_negative_incrementing_circuit
-- name    : CombOpt.MinCostFlow.optimal_iff_no_negative_incrementing_circuit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:45.55024+00:00
-- url     : https://prove2.me/theorems/be78ddc8-aab6-484e-9bd1-0901375257a3
-- title:
--   Theorem 4.2 — optimal iff no negative-cost $x$-incrementing circuit (corrected: a loop may be traversed in reverse)
-- statement:
--   Consider the minimum-cost flow problem (4.1) on a digraph $G$ with demands $b$ ($b(V)=0$), nonnegative capacities $u\in(\mathbb R\cup\{\infty\})^E$ and costs $c$. A feasible solution $x$ of (4.1) is optimal if and only if there is no $x$-incrementing circuit of negative $c$-cost:
--
--   $$x\ \text{optimal}\iff \neg\exists\,C\ \text{circuit}:\ C\ \text{is } x\text{-incrementing and}\ \sum_{e\text{ fwd in }C}c_e-\sum_{e\text{ rev in }C}c_e<0.$$
--
--   Here a loop may be traversed as a reverse arc (see the difference below). This is the optimality criterion behind cycle-cancelling algorithms.
--
--   Differences from the source:
--   - correction: a loop arc of a circuit is always forward (p. 19: forward iff t(e_i) = v_{i−1} and h(e_i) = v_i) → a circuit may traverse a loop forward or reverse; reason: counterexample: one node v, one loop e at v, b_v = 0, u_e = 1, c_e = 1, x_e = 1 is feasible but not optimal (x_e = 0 costs 0), yet the only circuit v, e, v has e forward with x_e = u_e, so no x-incrementing circuit exists; the book's proof uses the reverse arc of every arc with x_e > 0 in G(x), loops included
--   - encoding: capacities u ∈ (ℝ ∪ {∞})^E, u ≥ 0 → u : E → EReal with 0 ≤ u e, u e = ⊤ for u_e = ∞; reason: Lean convention; the same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 4.2, p. 94 (PDF p. 102)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalFlow
import Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit_cost
import Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit_IsIncrementing

namespace CombOpt.MinCostFlow

/-- **Theorem 4.2 (no negative-cost incrementing circuit; corrected: loops may be traversed in
reverse).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 4.2, p. 94 (PDF p. 102): "A feasible solution x of (4.1) is optimal if and only if
there is no x-incrementing circuit having negative c-cost."

**Formalization Note.** The standing assumptions of §4.1, p. 91 ("u ∈ (ℝ ∪ {∞})^E is nonnegative, and b(V) = 0"), are the hypotheses `hu` and `hb`; capacities are `EReal` with `u e = ⊤` for `u_e = ∞`. Circuits are `G.Circuit`, which allow a loop to be traversed in
reverse (see that definition). As printed, a loop is always forward, and the theorem fails: one
node `v`, one loop `e` at `v`, `b_v = 0`, `u_e = 1`, `c_e = 1`, `x_e = 1` is feasible but not
optimal (`x_e = 0` costs less), while the only circuit `v, e, v` has `e` forward with `x_e = u_e`,
so it is not x-incrementing. The book's own proof uses the reverse arc of every arc with
`x_e > 0` in `G(x)` (p. 93), loops included. -/
theorem optimal_iff_no_negative_incrementing_circuit {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Digraph V E) (b : V → ℝ) (u : E → EReal) (c : E → ℝ)
    (hb : ∑ v, b v = 0) (hu : ∀ e, 0 ≤ u e)
    (x : E → ℝ) (hx : G.IsFeasibleFlow b u x) :
    G.IsOptimalFlow b u c x ↔ ¬∃ C : G.Circuit, C.IsIncrementing u x ∧ C.cost c < 0 := by sorry

end CombOpt.MinCostFlow
