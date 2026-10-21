-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_claim_3_1
-- name    : BudgetedAffine.Budget.claim_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:28:01.141232+00:00
-- url     : https://prove2.me/theorems/8c5ff07d-bfa7-4c72-a06e-8a3a40279183
-- title:
--   Claim 3.1 — z(W) = ηγ · ẑ(W) for every W ⊆ J
-- statement:
--   Let $n\ge3$, $B\in\mathbb R^{m\times n}_+$, $d\in\mathbb R^n_+$, $\mathcal J\subseteq[m]$, $\gamma>0$ and $w_i\in(0,1]$ for $i\in\mathcal J$. Let $\eta=4\log n/\log\log n$ and let $\hat d$, $\hat B$ and $\hat z$ be the rescaled data and covering value (3.6) of Section 3.3. Then for every $\mathcal W\subseteq\mathcal J$,
--   $$z(\mathcal W)=\eta\gamma\cdot\hat z(\mathcal W).$$
--
--   The rescaling turns condition 1 of Lemma 3.3 into $\hat d_j\ge1$ and normalises $\hat B$ into $[0,1]$, which is what the randomized rounding of Claims 3.2 and 3.3 needs.
--
--   **Formalization Note** Both sides are extended-real covering values, so the identity includes the case where both are $+\infty$. The paper's appendix proof writes $\max_{k\in\mathcal W}$ where the definition of $\hat d,\hat B$ has $\max_{k\in\mathcal J}$; the statement uses the definition's $\mathcal J$. Condition 1 of Lemma 3.3 is not needed for the identity and is not assumed. $n\ge3$ makes $\eta>0$.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Claim 3.1, p. 12 (proof App. A, pp. 30–31)

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Budget_Rescaling

namespace BudgetedAffine.Budget

open Matrix

/-- Claim 3.1: with `η = 4 log n / log log n`, `γ > 0` and `wᵢ ∈ (0,1]` on `J`, the covering
value of every `W ⊆ J` is a scaling of the rescaled value (3.6): `z(W) = η γ · ẑ(W)`. -/
theorem claim_3_1 {m n : ℕ} (hn : 3 ≤ n) (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (J : Finset (Fin m)) (γ : ℝ) (w : Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hd : 0 ≤ d) (hγ : 0 < γ) (hw : ∀ i ∈ J, 0 < w i ∧ w i ≤ 1)
    (W : Finset (Fin m)) (hW : W ⊆ J) :
    coverCost B d (indic W) =
      ((beta n * γ : ℝ) : EReal) *
        coverCost (BHat B w J) (dHat B d w J (beta n) γ) (wIndic w W) := by sorry

end BudgetedAffine.Budget
