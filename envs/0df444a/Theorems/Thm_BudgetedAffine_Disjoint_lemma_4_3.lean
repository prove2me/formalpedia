-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_3
-- name    : BudgetedAffine.Disjoint.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:18:30.054487+00:00
-- url     : https://prove2.me/theorems/7404fb6d-8831-48b8-91fc-e4940ef82d7f
-- title:
--   Lemma 4.3 — the linear part costs at most βρ·OPT for every h ∈ U
-- statement:
--   In the setting of Lemma 4.2, with $n\ge3$ and $\beta=\dfrac{8\log n}{\log\log n}$, the cost of the linear part (4.5) satisfies
--   $$d^Ty_{Lin}(h)=d^T\sum_{i\in\mathcal I}\alpha_ih_iv_i\ \le\ \beta\,\rho\cdot\mathrm{OPT}\qquad\text{for every }h\in\mathcal U.$$
--
--   With $\rho=O(\log n)$ this is the paper's bound $O(\beta\log n)\cdot\mathrm{OPT}$, which is $O(\log^2n/\log\log n)\cdot\mathrm{OPT}$.
--
--   **Formalization Note** The $O(\log n)$ factor is the competitive ratio $\rho$ of the online algorithm, made explicit. The hypothesis $n\ge3$ is added so that $\beta>0$ ($\log\log2<0$). The hypothesis $c^Tx\ge0$ on $\mathcal X$ is added as in Lemma 4.1.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 4.3, p. 18

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction

namespace BudgetedAffine.Disjoint

open Matrix

/-- Lemma 4.3: for `n ≥ 3`, the cost of the linear part (4.5) is at most `β ρ · OPT` for every
`h` in the disjoint constrained budgeted set, with `β = 8 log n / log log n` and `ρ` the competitive
ratio of the online covering algorithm (the paper's `O(β log n) · OPT`). -/
theorem lemma_4_3 {m n L : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : BudgetedAffine.Budget.IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hS : IsPartition S) (hw : ∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : BudgetedAffine.Budget.IsOptimalAR A B c d X (disjointBudgetSet S w) xs ys)
    (OPT : ℝ) (hOPT : BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) = (OPT : EReal))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (alg : OnlineCover (Btil A B xs) d ρ)
    (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m))
    (ha : IsGreedyRun alg w (hatS S A xs) σ a)
    (hn : 3 ≤ n) (v : Fin m → Fin n → ℝ)
    (hv : ∀ i ∈ Iset A B d S w xs σ (nuInc alg a), BudgetedAffine.Budget.IsCoverOpt B d (Pi.single i 1) (v i)) :
    ∀ h ∈ disjointBudgetSet S w,
      d ⬝ᵥ BudgetedAffine.Budget.yLin (Iset A B d S w xs σ (nuInc alg a)) (BudgetedAffine.Budget.alpha A xs) v h ≤ beta8 n * ρ * OPT := by sorry

end BudgetedAffine.Disjoint
