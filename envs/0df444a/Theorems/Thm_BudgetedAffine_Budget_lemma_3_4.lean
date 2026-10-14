-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_lemma_3_4
-- name    : BudgetedAffine.Budget.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:52.98777+00:00
-- url     : https://prove2.me/theorems/eab34111-acae-4907-88fd-bce5c3a4d5cc
-- title:
--   Lemma 3.4 — the static part costs z_Sta = O(β)·OPT
-- statement:
--   There are constants $C>0$ and $N$ such that for every $n\ge N$, every $m$ and every instance of (1.1) — $A\in\mathbb R^{m\times n}$, $B\in\mathbb R^{m\times n}_+$, $c,d\in\mathbb R^n_+$, a polyhedral $\mathcal X$ with $c^Tx\ge0$ on $\mathcal X$, and weights $w_i\in[0,1]$ of the budget set $\mathcal U$ — the following holds. If $(x^*,y^*)$ is an optimal solution, $\mathrm{OPT}=z_{AR}(\mathcal U)$ is finite, $\alpha_i=1-(Ax^*)_i$ and $\mathcal I$ is the threshold set of Section 3.1, then the value of the static problem (3.4) satisfies
--   $$z_{Sta}\le C\,\beta\cdot\mathrm{OPT},\qquad\beta=\frac{4\log n}{\log\log n}.$$
--
--   This bounds the cost of the static part of the affine solution (3.5); with Lemmas 3.1 and 3.2 it gives Theorem 3.1.
--
--   **Formalization Note** "$O(\beta)\cdot\mathrm{OPT}$" is formalized with $C$ and $N$ chosen before $m$ and the instance. The proof gives $z_{Sta}\le(1+\beta)\mathrm{OPT}$. $z_{Sta}$ is the extended-real value of (3.4). The hypothesis $c^Tx\ge0$ on $\mathcal X$ is added to the paper's model (it gives $\mathrm{OPT}\ge0$).
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 3.4, p. 10 (proof pp. 10–11)

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction

namespace BudgetedAffine.Budget

open Matrix

/-- Lemma 3.4: the cost `z_Sta` of the static problem (3.4) is `O(β) · OPT`, with the constant
`C` and the threshold `N` uniform over `m` and every instance. -/
theorem lemma_3_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
      (c d : Fin n → ℝ) (X : Set (Fin n → ℝ)) (w : Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → IsPolyhedral X →
      (∀ x ∈ X, 0 ≤ c ⬝ᵥ x) → (∀ i, 0 ≤ w i ∧ w i ≤ 1) →
      ∀ (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ),
      IsOptimalAR A B c d X (budgetSet w) xs ys →
      ∀ OPT : ℝ, zAR A B c d X (budgetSet w) = (OPT : EReal) →
      staticValue A B c d X (staRhs (Iset A B d w xs OPT) (alpha A xs)) ≤
        ((C * beta n * OPT : ℝ) : EReal) := by sorry

end BudgetedAffine.Budget
