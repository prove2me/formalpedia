-- Prove2me | Theorems.Thm_CombOpt_MinCostFlow_exists_integral_optimal_flow
-- name    : CombOpt.MinCostFlow.exists_integral_optimal_flow
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:35.011798+00:00
-- url     : https://prove2.me/theorems/5622f996-7106-4ea1-9044-2e2886213aa9
-- title:
--   Theorem 4.5 — integral demands and capacities give an integral optimal flow
-- statement:
--   Consider the minimum-cost flow problem (4.1)
--
--   $$\text{minimize }\sum(c_e x_e : e\in E)\ \text{ subject to } f_x(v)=b_v\ (v\in V),\ 0\le x_e\le u_e\ (e\in E)$$
--
--   on a digraph $G=(V,E)$ with demands $b\in\mathbb R^V$, $b(V)=0$, nonnegative capacities $u\in(\mathbb R\cup\{\infty\})^E$ and arbitrary real costs $c$. If $b$ and $u$ are integral (the finite capacities are integers) and (4.1) has an optimal solution, then it has an optimal solution $x$ with every $x_e$ an integer.
--
--   This is the integrality theorem for minimum-cost flows: the minimum-cost integral flow problem is no harder than its linear relaxation, which is why shortest paths, transportation, assignment and maximum flow problems all have integral optima.
--
--   Differences from the source:
--   - encoding: capacities u ∈ (ℝ ∪ {∞})^E, u ≥ 0 → u : E → EReal with 0 ≤ u e, u e = ⊤ for u_e = ∞; reason: Lean convention; the same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 4.5, p. 95 (PDF p. 103)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalFlow
import Definitions.Def_CombOpt_MinCostFlow_IsIntegralExt

namespace CombOpt.MinCostFlow

/-- **Theorem 4.5 (integral optimal flows).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 4.5, p. 95 (PDF p. 103): "If b and u are integral and (4.1) has an optimal solution,
then it has an optimal solution that is integral."

**Formalization Note.** The standing assumptions of §4.1, p. 91 ("u ∈ (ℝ ∪ {∞})^E is nonnegative, and b(V) = 0"), are the hypotheses `hu` and `hb`; capacities are `EReal` with `u e = ⊤` for `u_e = ∞`. "u integral" means the finite components of `u` are integers
(p. 39, `IsIntegralExt`). The costs `c` are arbitrary reals. -/
theorem exists_integral_optimal_flow {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Digraph V E) (b : V → ℝ) (u : E → EReal) (c : E → ℝ)
    (hb : ∑ v, b v = 0) (hu : ∀ e, 0 ≤ u e)
    (hbint : ∀ v, ∃ k : ℤ, b v = k) (huint : ∀ e, IsIntegralExt (u e))
    (hopt : ∃ x, G.IsOptimalFlow b u c x) :
    ∃ x, G.IsOptimalFlow b u c x ∧ ∀ e, ∃ k : ℤ, x e = k := by sorry

end CombOpt.MinCostFlow
