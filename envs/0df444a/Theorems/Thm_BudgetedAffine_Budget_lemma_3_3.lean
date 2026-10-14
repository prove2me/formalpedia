-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_lemma_3_3
-- name    : BudgetedAffine.Budget.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:29.779067+00:00
-- url     : https://prove2.me/theorems/4bf4740f-8c4f-425f-8521-bcc2b4d1c739
-- title:
--   Lemma 3.3 (structural result) — z(J) ≤ 4γ log n / log log n under conditions 1 and 2
-- statement:
--   There is $N_0$ such that for every $n\ge N_0$ the following holds. Let $B\in\mathbb R^{m\times n}_+$, $d\in\mathbb R^n_+$ and $\mathcal J\subseteq[m]$, and let $z(\cdot)$ be the covering value (3.2). Suppose $\gamma>0$ and $w_i\in(0,1]$ for $i\in\mathcal J$ satisfy
--
--   1. for all $i\in\mathcal J$, $\dfrac{z(e_i)}{w_i}>4\gamma\cdot\dfrac{\log n}{\log\log n}$;
--   2. for all $\mathcal W\subseteq\mathcal J$, $\sum_{i\in\mathcal W}w_i\le1$ implies $z(\mathcal W)\le\gamma$.
--
--   Then
--   $$z(\mathcal J)\le4\gamma\cdot\frac{\log n}{\log\log n}.$$
--
--   This structural result on fractional covering bounds the cost of covering all of $\mathcal J$ when every single row is expensive but every budget-feasible scenario is cheap; it is the key step in bounding the static part (Lemma 3.4).
--
--   **Formalization Note** The threshold $N_0$ is a correction: as printed, the lemma is false for $n=2$, where $\log\log2<0$ makes condition 1 vacuous and the bound negative (e.g. $m=n=2$, $B=I$, $d=(1,1)$, $\mathcal J=\{1\}$, $w_1=\gamma=1$: then $z(\mathcal J)=1$). The paper's proof itself needs "$n$ sufficiently large". $N_0$ depends on nothing else: it is chosen before $m$, $B$, $d$, $\mathcal J$, $\gamma$ and $w$. Condition 1 is stated in the multiplied form $z(e_i)>4\gamma\frac{\log n}{\log\log n}w_i$, equivalent since $w_i>0$. Covering values are extended reals, so an uncoverable row ($z(e_i)=+\infty$) satisfies condition 1, as on the page.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 3.3, p. 9 (proof Sec. 3.3, pp. 12–14)

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model

namespace BudgetedAffine.Budget

open Matrix

/-- Lemma 3.3 (structural result), for all `n` beyond a threshold `N₀` that is uniform in every
other datum: if `γ > 0`, `wᵢ ∈ (0,1]` on `J`, (1) `z(eᵢ)/wᵢ > 4γ log n / log log n` for every
`i ∈ J`, and (2) `∑_{i ∈ W} wᵢ ≤ 1` implies `z(W) ≤ γ` for every `W ⊆ J`, then
`z(J) ≤ 4γ log n / log log n`. -/
theorem lemma_3_3 :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (m : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
      (J : Finset (Fin m)) (γ : ℝ) (w : Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ d → 0 < γ → (∀ i ∈ J, 0 < w i ∧ w i ≤ 1) →
      (∀ i ∈ J, ((4 * γ * (Real.log n / Real.log (Real.log n)) * w i : ℝ) : EReal) <
        coverCost B d (Pi.single i 1)) →
      (∀ W ⊆ J, ∑ i ∈ W, w i ≤ 1 → coverCost B d (indic W) ≤ (γ : EReal)) →
      coverCost B d (indic J) ≤ ((4 * γ * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) := by sorry

end BudgetedAffine.Budget
