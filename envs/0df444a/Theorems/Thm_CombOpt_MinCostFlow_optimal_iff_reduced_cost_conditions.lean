-- Prove2me | Theorems.Thm_CombOpt_MinCostFlow_optimal_iff_reduced_cost_conditions
-- name    : CombOpt.MinCostFlow.optimal_iff_reduced_cost_conditions
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:32.413181+00:00
-- url     : https://prove2.me/theorems/14e3c687-70c5-4f17-aaca-75ef2b7c6617
-- title:
--   Theorem 4.1 — reduced-cost optimality conditions for minimum-cost flows
-- statement:
--   Consider the minimum-cost flow problem (4.1) on a digraph $G=(V,E)$ with demands $b$ ($b(V)=0$), nonnegative capacities $u\in(\mathbb R\cup\{\infty\})^E$ and costs $c$. For $y\in\mathbb R^V$ write $\bar c_{vw}=c_{vw}+y_v-y_w$.
--
--   1. A feasible solution $x$ of (4.1) is optimal if and only if there exists $y\in\mathbb R^V$ such that for each $e\in E$:
--   $$\bar c_e<0\ \Rightarrow\ x_e=u_e\ (\neq\infty),\qquad \bar c_e>0\ \Rightarrow\ x_e=0.$$
--   2. Moreover, every pair $(x,y)$ in which $x$ is an optimal solution of (4.1) and $y$ is an optimal dual solution (extends to an optimal solution $(y,z)$ of the dual (4.3)) satisfies these conditions.
--
--   This is the complementary slackness characterization of optimality on which the primal and primal–dual minimum-cost flow algorithms rest.
--
--   Differences from the source:
--   - encoding: capacities u ∈ (ℝ ∪ {∞})^E, u ≥ 0 → u : E → EReal with 0 ≤ u e, u e = ⊤ for u_e = ∞; reason: Lean convention; the same instances
--   - encoding: no dual variable z_vw when u_vw = ∞ → z indexed by the subtype {e // u e ≠ ⊤}; reason: the same dual program
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 4.1, p. 93 (PDF p. 101); dual (4.3), p. 92

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalFlow
import Definitions.Def_CombOpt_MinCostFlow_Digraph_SatisfiesOptimalityConditions
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalDual

namespace CombOpt.MinCostFlow

/-- **Theorem 4.1 (reduced-cost optimality conditions).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 4.1, p. 93 (PDF p. 101): "A feasible solution x of (4.1) is optimal if and only if
there exists a vector (y_v : v ∈ V) satisfying for each e ∈ E: c̄_e < 0 implies x_e = u_e (≠ ∞),
c̄_e > 0 implies x_e = 0. Moreover, every pair (x, y) of optimal primal and dual solutions
satisfies these conditions."

**Formalization Note.** The standing assumptions of §4.1, p. 91 ("u ∈ (ℝ ∪ {∞})^E is nonnegative, and b(V) = 0"), are the hypotheses `hu` and `hb`; capacities are `EReal` with `u e = ⊤` for `u_e = ∞`. "y is an optimal dual solution" means, as on p. 92, that `y`
extends to an optimal solution `(y, z)` of (4.3). -/
theorem optimal_iff_reduced_cost_conditions {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Digraph V E) (b : V → ℝ) (u : E → EReal) (c : E → ℝ)
    (hb : ∑ v, b v = 0) (hu : ∀ e, 0 ≤ u e) :
    (∀ x : E → ℝ, G.IsFeasibleFlow b u x →
      (G.IsOptimalFlow b u c x ↔ ∃ y : V → ℝ, G.SatisfiesOptimalityConditions u c x y)) ∧
    ∀ (x : E → ℝ) (y : V → ℝ), G.IsOptimalFlow b u c x →
      (∃ z : {e : E // u e ≠ ⊤} → ℝ, G.IsOptimalDual b u c y z) →
        G.SatisfiesOptimalityConditions u c x y := by sorry

end CombOpt.MinCostFlow
