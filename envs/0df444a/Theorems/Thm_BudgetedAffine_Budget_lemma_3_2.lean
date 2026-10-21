-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_lemma_3_2
-- name    : BudgetedAffine.Budget.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:52.026218+00:00
-- url     : https://prove2.me/theorems/00dc301d-2886-4ec1-b0eb-56b285b20983
-- title:
--   Lemma 3.2 — the linear part y_Lin(h) costs at most β·OPT for every h ∈ U
-- statement:
--   In the setting of Section 3.1 — problem (1.1) with $B\ge0$, $c,d\ge0$, polyhedral $\mathcal X$ with $c^Tx\ge0$ on $\mathcal X$, the budget set $\mathcal U$ with weights $w_i\in[0,1]$, an optimal solution $(x^*,y^*)$, $\mathrm{OPT}=z_{AR}(\mathcal U)$, $\alpha_i=1-(Ax^*)_i$, $\beta=4\log n/\log\log n$, the threshold set $\mathcal I$, and optimal covering solutions $v_i$ of $z(e_i)$ for $i\in\mathcal I$ — suppose $n\ge3$. Then for every $h\in\mathcal U$ the linear part $y_{Lin}(h)=\sum_{i\in\mathcal I}\alpha_ih_iv_i$ satisfies
--   $$d^Ty_{Lin}(h)\le\beta\cdot\mathrm{OPT}.$$
--
--   This bounds the cost of the linear part of the affine solution (3.5).
--
--   **Formalization Note** $n\ge3$ is added: for $n=2$, $\log\log 2<0$ makes $\beta<0$ and the bound false whenever $\mathrm{OPT}>0$; for $n\ge3$, $\beta>0$. As in Lemma 3.1, $v_i$ is required to be optimal only for $i\in\mathcal I$, and $c^Tx\ge0$ on $\mathcal X$ is the mission's added model hypothesis.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 3.2, p. 9

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction

namespace BudgetedAffine.Budget

open Matrix

/-- Lemma 3.2: the cost of the linear part `y_Lin(h)` of (3.3) is at most `β · OPT` for every
`h ∈ U`. -/
theorem lemma_3_2 {m n : ℕ} (hn : 3 ≤ n) (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (w : Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : IsOptimalAR A B c d X (budgetSet w) xs ys)
    (OPT : ℝ) (hOPT : zAR A B c d X (budgetSet w) = (OPT : EReal))
    (v : Fin m → Fin n → ℝ)
    (hv : ∀ i ∈ Iset A B d w xs OPT, IsCoverOpt B d (Pi.single i 1) (v i)) :
    ∀ h ∈ budgetSet w, d ⬝ᵥ yLin (Iset A B d w xs OPT) (alpha A xs) v h ≤ beta n * OPT := by sorry

end BudgetedAffine.Budget
