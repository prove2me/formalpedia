-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_4
-- name    : BudgetedAffine.Disjoint.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:18:29.004798+00:00
-- url     : https://prove2.me/theorems/8c0d4c05-229a-4b47-869f-e7a4bf3b1c70
-- title:
--   Lemma 4.4 — the static part costs at most (1 + 2ρ + βρ)·OPT
-- statement:
--   There is a threshold $N$ such that for every $n\ge N$ the following holds. In the setting of Lemma 4.1 (an instance of (1.1) with $n$ decision variables over a disjoint constrained budgeted set, an optimal solution $(x^*,y^*)$ with value $\mathrm{OPT}$, an online covering algorithm for $\tilde B$ with competitive ratio $\rho\ge0$, a run of Algorithm 1), the value of the static problem (4.6) satisfies
--   $$z_{Sta}\ \le\ (1+2\rho+\beta\rho)\cdot\mathrm{OPT},\qquad \beta=\frac{8\log n}{\log\log n}.$$
--   $N$ does not depend on $m$, $L$, $\rho$, the algorithm or the instance.
--
--   With $\rho=O(\log n)$ this is the paper's $O(\beta\log n)\cdot\mathrm{OPT}$; the three terms are the paper's final bound $\mathrm{OPT}+O(\log n)\cdot\mathrm{OPT}+O(\beta\log n)\cdot\mathrm{OPT}$ (p. 20).
--
--   **Formalization Note** The $O(\log n)$ factor is the competitive ratio $\rho$, made explicit; the explicit constant is the one the proof prints. The threshold $N$ is that of Lemma 3.3, which the proof applies; it is quantified before every other datum. The hypothesis $c^Tx\ge0$ on $\mathcal X$ is added as in Lemma 4.1. The weights may be $0$ (as (4.1) allows), while Lemma 3.3 needs $w\in(0,1]$; the proof must give such components a small positive weight — a gap in the paper's proof, not a change to the statement.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 4.4, pp. 19–20

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction

namespace BudgetedAffine.Disjoint

open Matrix

/-- Lemma 4.4: the cost `z_Sta` of the static problem (4.6) is at most
`(1 + 2ρ + βρ) · OPT` (the paper's `O(β log n) · OPT`, with `ρ` the competitive ratio of the online
covering algorithm and `β = 8 log n / log log n`), for every `n` beyond a threshold `N` that is
uniform over `m`, `L`, `ρ` and every instance. -/
theorem lemma_4_4 :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (m L : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
      (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → BudgetedAffine.Budget.IsPolyhedral X →
      (∀ x ∈ X, 0 ≤ c ⬝ᵥ x) → IsPartition S → (∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1) →
      ∀ (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ),
      BudgetedAffine.Budget.IsOptimalAR A B c d X (disjointBudgetSet S w) xs ys →
      ∀ OPT : ℝ, BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) = (OPT : EReal) →
      ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (alg : OnlineCover (Btil A B xs) d ρ)
        (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m)),
      IsGreedyRun alg w (hatS S A xs) σ a →
      BudgetedAffine.Budget.staticValue A B c d X (BudgetedAffine.Budget.staRhs (Iset A B d S w xs σ (nuInc alg a)) (BudgetedAffine.Budget.alpha A xs)) ≤
        (((1 + 2 * ρ + beta8 n * ρ) * OPT : ℝ) : EReal) := by sorry

end BudgetedAffine.Disjoint
