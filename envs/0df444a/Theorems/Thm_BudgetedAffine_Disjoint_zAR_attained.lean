-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_zAR_attained
-- name    : BudgetedAffine.Disjoint.zAR_attained
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T21:16:30.561087+00:00
-- url     : https://prove2.me/theorems/d369fcb4-4785-4658-8ff8-0ac6831fb755
-- title:
--   The adjustable robust problem (1.1) over a disjoint constrained budgeted set attains its optimum
-- statement:
--   Consider the two-stage adjustable robust problem (1.1),
--   $$z_{AR}(\mathcal U)=\min_{x\in\mathcal X}\Big(c^\top x+\max_{h\in\mathcal U}\ \min_{y(h)\ge0}\{d^\top y(h): Ax+By(h)\ge h\}\Big),$$
--   with the following data:
--
--   1. $A\in\mathbb R^{m\times n}$, $B\in\mathbb R^{m\times n}_+$ and $c,d\in\mathbb R^n_+$;
--   2. $\mathcal X$ is a polyhedron with $c^\top x\ge0$ for all $x\in\mathcal X$;
--   3. $\mathcal U$ is the disjoint constrained budgeted set (4.1) for a partition $S_1,\dots,S_L$ of $[m]$ and weights $w_{\ell i}\in[0,1]$.
--
--   If $z_{AR}(\mathcal U)<+\infty$, then the problem has an optimal solution. That is, there are $x^*\in\mathcal X$ and a recourse map $h\mapsto y^*(h)$, feasible for every $h\in\mathcal U$, whose worst-case cost $\sup_{h\in\mathcal U}\big(c^\top x^*+d^\top y^*(h)\big)$ equals $z_{AR}(\mathcal U)$.
--
--   The paper takes this optimal solution $(x^*,y^*(h))$ as the starting point of its construction (Sections 3.1 and 4.1, where $\alpha_i=1-(Ax^*)_i$). The existence holds because $\mathcal U$ is a polytope, so (1.1) is equivalent to a finite linear program over the vertices of $\mathcal U$.
--
--   **Formalization Note** $z_{AR}$ is the $\mathrm{EReal}$-valued infimum `zAR` of definition `BudgetedAffine_Budget_Model` (it is $+\infty$ when infeasible), and optimality is `IsOptimalAR`.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Sec. 3.1 p. 7 and Sec. 4.1 p. 15 (an optimal solution (x*, y*(h)) of (1.1) is fixed); existence of an optimal solution of the finite LP reformulation follows from Bertsimas–Tsitsiklis, Introduction to Linear Optimization, Corollary 2.3, p. 67

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover

namespace BudgetedAffine.Disjoint

open Matrix

/-- The two-stage adjustable robust problem (1.1) over a disjoint constrained budgeted set (4.1)
has an optimal solution `(x*, y*(·))` whenever its value `z_AR(U)` is finite. -/
theorem zAR_attained {m n L : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : BudgetedAffine.Budget.IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hS : IsPartition S) (hw : ∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1)
    (hfin : BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) ≠ ⊤) :
    ∃ (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ),
      BudgetedAffine.Budget.IsOptimalAR A B c d X (disjointBudgetSet S w) xs ys := by sorry

end BudgetedAffine.Disjoint
