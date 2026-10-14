-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_lemma_3_3
-- name    : BudgetedAffine.Disjoint.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:49.26188+00:00
-- url     : https://prove2.me/theorems/15b953bc-b383-4c74-b056-3ef0b682a69f
-- title:
--   Lemma 3.3 — structural result for fractional covering (for all sufficiently large n)
-- statement:
--   Let $B\in\mathbb R^{m\times n}_+$, $d\in\mathbb R^n_+$, $\mathcal J\subseteq[m]$, and let $z(h)=\min_{y\ge0}\{d^Ty: By\ge h\}$ be the covering value (3.2), with $z(\mathcal W)=z(\mathbb 1(\mathcal W))$. Suppose there are $\gamma>0$ and weights $w_i\in(0,1]$, $i\in\mathcal J$, such that
--   1. for all $i\in\mathcal J$, $\dfrac{z(e_i)}{w_i}>4\gamma\cdot\dfrac{\log n}{\log\log n}$;
--   2. for all $\mathcal W\subseteq\mathcal J$, $\sum_{i\in\mathcal W}w_i\le1$ implies $z(\mathcal W)\le\gamma$.
--
--   Then
--   $$z(\mathcal J)\le 4\gamma\cdot\frac{\log n}{\log\log n}.$$
--   The statement is asserted for every $n\ge N_0$, for a threshold $N_0$ that does not depend on $m$, $B$, $d$, $\mathcal J$, $\gamma$ or $w$.
--
--   In Section 4 the lemma is applied to the rescaled matrix $\tilde B$ with $\gamma=2(\nu_\ell-\nu_{\ell-1})$ to bound the cost of the expensive components of each block.
--
--   **Formalization Note** As printed (without a threshold) the lemma is false for $n=2$: there $\log\log2<0$, condition 1 is vacuous, and the conclusion bounds $z(\mathcal J)$ by a negative number (e.g. $m=n=2$, $B=I$, $d=(1,1)$, $\mathcal J=\{1\}$, $w_1=1$, $\gamma=1$, $z(\mathcal J)=1$). The paper's proof needs "$n$ sufficiently large" (App. A), so the Lean asserts it for $n\ge N_0$, with $N_0$ quantified before every other datum. Condition 1 is written in the equivalent multiplied form $z(e_i)>4\gamma\frac{\log n}{\log\log n}w_i$ ($w_i>0$). Covering values are extended reals, so $z(e_i)=+\infty$ satisfies condition 1 as on the page. This is the same statement as Lemma 3.3 in the first mission of this series, restated here because draft missions cannot import each other.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 3.3, p. 9

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model

namespace BudgetedAffine.Disjoint

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
        BudgetedAffine.Budget.coverCost B d (Pi.single i 1)) →
      (∀ W ⊆ J, ∑ i ∈ W, w i ≤ 1 → BudgetedAffine.Budget.coverCost B d (BudgetedAffine.Budget.indic W) ≤ (γ : EReal)) →
      BudgetedAffine.Budget.coverCost B d (BudgetedAffine.Budget.indic J) ≤ ((4 * γ * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) := by sorry

end BudgetedAffine.Disjoint
