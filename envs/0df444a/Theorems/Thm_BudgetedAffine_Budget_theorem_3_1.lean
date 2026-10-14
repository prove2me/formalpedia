-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_theorem_3_1
-- name    : BudgetedAffine.Budget.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:20.816324+00:00
-- url     : https://prove2.me/theorems/2fa8f110-ec2d-4a50-a895-498e344235c7
-- title:
--   Theorem 3.1 — for budget of uncertainty sets, z_Aff(U) = O(log n / log log n)·z_AR(U)
-- statement:
--   Consider the two-stage adjustable robust problem (1.1): $A\in\mathbb R^{m\times n}$, a non-negative recourse matrix $B\in\mathbb R^{m\times n}_+$, costs $c,d\in\mathbb R^n_+$, and a polyhedral first-stage set $\mathcal X$ on which $c^Tx\ge0$, where $n$ is the number of decision variables. Let $\mathcal U$ be the budget of uncertainty set (1.2),
--   $$\mathcal U=\Big\{h\in[0,1]^m:\ \sum_{i=1}^mw_ih_i\le1\Big\},\qquad w_i\in[0,1].$$
--   There are constants $C>0$ and $N$ such that for every $n\ge N$, every $m$ and every such instance,
--   $$z_{Aff}(\mathcal U)\le C\cdot\frac{\log n}{\log\log n}\cdot z_{AR}(\mathcal U).$$
--
--   That is, the best affine policy is within a factor $O(\log n/\log\log n)$ of the optimal adjustable solution, which matches the $\Omega(\log n/\log\log n)$ hardness of approximation of Feige et al. for this problem.
--
--   **Formalization Note** $C$ and $N$ are chosen before $m$, the matrices, the costs, $\mathcal X$ and $w$, so the constant is uniform over all instances; $N$ also absorbs $n\le2$, where $\log\log n\le0$. Both values are extended reals, $+\infty$ when infeasible; $z_{AR}\ge0$ under the hypotheses, and if $z_{AR}=+\infty$ the bound holds trivially, as on the page. The hypothesis $c^Tx\ge0$ for $x\in\mathcal X$ is added: without it the theorem is false ($z_{AR}<0$ forces $z_{Aff}\le C\frac{\log n}{\log\log n}z_{AR}<z_{AR}\le z_{Aff}$ once $C\frac{\log n}{\log\log n}>1$), and the paper's proof uses $\mathrm{OPT}\ge0$. It holds whenever $\mathcal X\subseteq\mathbb R^n_+$.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Theorem 3.1, p. 7 (proof p. 11)

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model

namespace BudgetedAffine.Budget

open Matrix

/-- Theorem 3.1: for budget of uncertainty sets, `z_Aff(U) = O(log n / log log n) · z_AR(U)`,
with the constant `C` and the threshold `N` uniform over `m` and every instance. -/
theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
      (c d : Fin n → ℝ) (X : Set (Fin n → ℝ)) (w : Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → IsPolyhedral X →
      (∀ x ∈ X, 0 ≤ c ⬝ᵥ x) → (∀ i, 0 ≤ w i ∧ w i ≤ 1) →
      zAff A B c d X (budgetSet w) ≤
        ((C * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) *
          zAR A B c d X (budgetSet w) := by sorry

end BudgetedAffine.Budget
