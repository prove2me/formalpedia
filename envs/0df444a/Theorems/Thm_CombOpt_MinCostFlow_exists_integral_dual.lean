-- Prove2me | Theorems.Thm_CombOpt_MinCostFlow_exists_integral_dual
-- name    : CombOpt.MinCostFlow.exists_integral_dual
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:41.034869+00:00
-- url     : https://prove2.me/theorems/610f87e0-ef98-434f-8039-566dbad76bab
-- title:
--   Theorem 4.3 — integral dual solutions for integral costs
-- statement:
--   Consider the minimum-cost flow problem (4.1) on a digraph $G$ with demands $b$ ($b(V)=0$), nonnegative capacities $u\in(\mathbb R\cup\{\infty\})^E$ and costs $c$. Suppose that (4.1) has an optimal solution and $c$ is integral. Then
--
--   1. for every optimal solution $x$, the vector $y$ of Theorem 4.1 can be chosen integral: there is $y\in\mathbb Z^V$ with $\bar c_e<0\Rightarrow x_e=u_e\ (\neq\infty)$ and $\bar c_e>0\Rightarrow x_e=0$ for all $e$;
--   2. equivalently, the dual linear program (4.3) has an optimal solution $(y,z)$ that is integral.
--
--   Integral potentials are what make the minimum-cost flow problem a source of totally dual integral systems.
--
--   Differences from the source:
--   - reading: y in Theorem 4.1 can be chosen integral; equivalently, (4.3) has an integral optimal solution → both forms as a conjunction: for every optimal x an integral y satisfying Theorem 4.1's conditions with x, and an integral optimal (y, z) of (4.3); reason: the book asserts both and calls them equivalent; stating both is the full claim
--   - encoding: capacities u ∈ (ℝ ∪ {∞})^E, u ≥ 0 → u : E → EReal with 0 ≤ u e, u e = ⊤ for u_e = ∞; reason: Lean convention; the same instances
--   - encoding: no dual variable z_vw when u_vw = ∞ → z indexed by the subtype {e // u e ≠ ⊤}; reason: the same dual program
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 4.3, p. 94 (PDF p. 102)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalFlow
import Definitions.Def_CombOpt_MinCostFlow_Digraph_SatisfiesOptimalityConditions
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalDual

namespace CombOpt.MinCostFlow

/-- **Theorem 4.3 (integral dual solutions).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 4.3, p. 94 (PDF p. 102): "Suppose that (4.1) has an optimal solution and c is
integral. Then y in Theorem 4.1 can be chosen integral; equivalently, the dual
linear-programming problem of (4.1) has an optimal solution that is integral."

**Formalization Note.** The standing assumptions of §4.1, p. 91 ("u ∈ (ℝ ∪ {∞})^E is nonnegative, and b(V) = 0"), are the hypotheses `hu` and `hb`; capacities are `EReal` with `u e = ⊤` for `u_e = ∞`. Both forms are stated: for every optimal `x` there is an integral
`y` satisfying the conditions of Theorem 4.1 with `x`, and (4.3) has an optimal solution `(y, z)`
with `y` and `z` integral. -/
theorem exists_integral_dual {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Digraph V E) (b : V → ℝ) (u : E → EReal) (c : E → ℝ)
    (hb : ∑ v, b v = 0) (hu : ∀ e, 0 ≤ u e)
    (hopt : ∃ x, G.IsOptimalFlow b u c x) (hc : ∀ e, ∃ k : ℤ, c e = k) :
    (∀ x : E → ℝ, G.IsOptimalFlow b u c x →
      ∃ y : V → ℝ, (∀ v, ∃ k : ℤ, y v = k) ∧ G.SatisfiesOptimalityConditions u c x y) ∧
    ∃ (y : V → ℝ) (z : {e : E // u e ≠ ⊤} → ℝ), G.IsOptimalDual b u c y z ∧
      (∀ v, ∃ k : ℤ, y v = k) ∧ ∀ e, ∃ k : ℤ, z e = k := by sorry

end CombOpt.MinCostFlow
