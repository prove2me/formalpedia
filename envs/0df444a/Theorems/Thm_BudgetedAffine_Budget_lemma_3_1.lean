-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_lemma_3_1
-- name    : BudgetedAffine.Budget.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:27:29.454329+00:00
-- url     : https://prove2.me/theorems/7bc293e0-7e7a-493f-a3c5-df9466a064c0
-- title:
--   Lemma 3.1 — the affine solution (3.5) is feasible for (1.1)
-- statement:
--   Consider problem (1.1) with $A\in\mathbb R^{m\times n}$, $B\in\mathbb R^{m\times n}_+$, $c,d\in\mathbb R^n_+$, a polyhedral $\mathcal X$ with $c^Tx\ge0$ on $\mathcal X$, and the budget set $\mathcal U=\{h\in[0,1]^m:\sum_iw_ih_i\le1\}$ with $w_i\in[0,1]$. Let $(x^*,y^*)$ be an optimal solution and $\mathrm{OPT}=z_{AR}(\mathcal U)$ (finite). Let $\alpha_i=1-(Ax^*)_i$, let $\mathcal I$ be the threshold set of Section 3.1, let $v_i$ be an optimal solution of $\min_{y\ge0}\{d^Ty: By\ge e_i\}$ for each $i\in\mathcal I$, and let $(x_{Sta},y_{Sta})$ be an optimal solution of the static problem (3.4). Then the affine solution (3.5)
--   $$x=x_{Sta},\qquad y(h)=Ph+y_{Sta}=y_{Lin}(h)+y_{Sta},$$
--   where $P$ has $i$-th column $\alpha_iv_i$ for $i\in\mathcal I$ and $0$ otherwise, is feasible for (1.1): $x\in\mathcal X$, and $y(h)\ge0$, $Ax+By(h)\ge h$ for every $h\in\mathcal U$.
--
--   This is the feasibility half of the proof of Theorem 3.1; Lemmas 3.2 and 3.4 bound the cost of the same solution.
--
--   **Formalization Note** The paper takes $v_i$ for every $i\in[m]$; only $i\in\mathcal I$ is used, and for $i\notin\mathcal I$ an optimal $v_i$ may not exist (the row may be uncoverable by $B$ when $\alpha_i\le0$), so the hypothesis is required only on $\mathcal I$. The hypothesis $c^Tx\ge0$ on $\mathcal X$ is added to the paper's model, as in every statement of this mission (Theorem 3.1 is false without it).
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 3.1, p. 8

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction

namespace BudgetedAffine.Budget

open Matrix

/-- Lemma 3.1: the affine solution (3.5), `x = x_Sta`, `y(h) = P h + y_Sta` with `P h = y_Lin(h)`,
is feasible for (1.1) over the budget set. -/
theorem lemma_3_1 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (w : Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : IsOptimalAR A B c d X (budgetSet w) xs ys)
    (OPT : ℝ) (hOPT : zAR A B c d X (budgetSet w) = (OPT : EReal))
    (v : Fin m → Fin n → ℝ)
    (hv : ∀ i ∈ Iset A B d w xs OPT, IsCoverOpt B d (Pi.single i 1) (v i))
    (xSta ySta : Fin n → ℝ)
    (hSta : IsStaticOpt A B c d X (staRhs (Iset A B d w xs OPT) (alpha A xs)) xSta ySta) :
    Feasible A B X (budgetSet w) xSta
      (fun h => linMatrix (Iset A B d w xs OPT) (alpha A xs) v *ᵥ h + ySta) := by sorry

end BudgetedAffine.Budget
