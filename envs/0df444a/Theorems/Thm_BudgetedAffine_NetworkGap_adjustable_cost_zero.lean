-- Prove2me | Theorems.Thm_BudgetedAffine_NetworkGap_adjustable_cost_zero
-- name    : BudgetedAffine.NetworkGap.adjustable_cost_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:20.357033+00:00
-- url     : https://prove2.me/theorems/bce6946f-bd95-4f7f-a5b0-7923a2f209c7
-- title:
--   App. D, p. 35 — stocking J₁ fully gives an adjustable solution of cost 0
-- statement:
--   Consider the family of lot-sizing instances (7.2) with $m=2k$ nodes, bipartition $(J_1,J_2)$, $|J_1|=|J_2|=k$, budget uncertainty set $\mathcal U=\{h\in[0,1]^m:\sum_i h_i\le m/2\}$, inventory costs $c=0$ on $J_1$ and $c=1$ on $J_2$, unit capacities, and zero-cost shipping from $J_1$ to $J_2$. Let the first-stage inventory be
--   $$x_i=\begin{cases}1 & i\in J_1\\ 0 & i\in J_2.\end{cases}$$
--   Then there is a second-stage policy $y:\mathcal U\to\mathbb R_+^{J_1\times J_2}$ such that $(x,y)$ is feasible for (7.1) and, for every $h\in\mathcal U$,
--   $$\sum_{i=1}^m c_ix_i+\sum_{i\in J_1}\sum_{j\in J_2}d_{ij}\,y_{ij}(h)=0 .$$
--
--   Since every cost is non-negative, this shows $z_{AR}(\mathcal U)=0$: the fully adjustable problem has optimal value zero on the whole family.
--
--   **Formalization Note** The paper constructs $y(h)$ (a matching from $J_1\setminus\tilde J_1(h)$ to $\tilde J_2(h)$) only for scenarios $h$ that are extreme points of $\mathcal U$. Feasibility requires every $h\in\mathcal U$, and the statement quantifies over all of $\mathcal U$; it remains true, since for fixed $x$ the constraints are linear in $(h,y)$. Lean indices are 0-based; shipping is restricted to the arcs $J_1\times J_2$, the only arcs of finite distance.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, App. D, proof of Lemma 7.1, first paragraph ("First let us show that zAR = 0" to "Therefore, zAR(U) = 0."), p. 35

import Mathlib
import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing
import Definitions.Def_BudgetedAffine_NetworkGap_Instance

namespace BudgetedAffine.NetworkGap

/-- App. D, p. 35: with `x = 1` on `J₁` and `x = 0` on `J₂` there is a second-stage policy
`y` such that `(x, y)` is feasible for the family (7.2) and costs `0` in every scenario. -/
theorem adjustable_cost_zero (k : ℕ) :
    ∃ y : (Node k → ℝ) → Arc k → ℝ,
      (lotSizingFamily k).Feasible (Sum.elim (fun _ => 1) (fun _ => 0)) y ∧
      ∀ h ∈ (lotSizingFamily k).U,
        (lotSizingFamily k).cost (Sum.elim (fun _ => 1) (fun _ => 0)) (y h) = 0 := by sorry

end BudgetedAffine.NetworkGap
