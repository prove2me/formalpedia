-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_1
-- name    : BudgetedAffine.Disjoint.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:18:21.73723+00:00
-- url     : https://prove2.me/theorems/758c393a-2ba5-42d4-a3f0-97a148c1cbb7
-- title:
--   Lemma 4.1 — the online cost ν_L of the greedy scenario is at most ρ·OPT
-- statement:
--   Consider (1.1) with $\mathcal U$ the disjoint constrained budgeted set (4.1) over a partition $S_1,\dots,S_L$ of $[m]$ with weights $w_{\ell i}\in[0,1]$, data $B\ge0$, $c,d\ge0$, $\mathcal X$ polyhedral with $c^Tx\ge0$ on $\mathcal X$. Let $(x^*,y^*)$ be an optimal solution with value $\mathrm{OPT}=z_{AR}(\mathcal U)$, let $\mathcal A$ be an online covering algorithm for $\tilde B$ with competitive ratio $\rho\ge0$, and let $a_1,\dots,a_L$ be a run of Algorithm 1. Then
--   $$\nu_L=\mathcal A(a_1,\dots,a_L)\ \le\ \rho\cdot\mathrm{OPT}.$$
--
--   With Buchbinder–Naor's algorithm, $\rho=O(\log n)$, which is the paper's $\nu_L=O(\log n)\cdot\mathrm{OPT}$. The bound feeds both the linear-part bound (Lemma 4.3) and the static-part bound (Lemma 4.4).
--
--   **Formalization Note** The paper's $O(\log n)$ is the competitive ratio of the online algorithm; it is written as the parameter $\rho$ of an arbitrary algorithm with that ratio. "$\nu_L=O(\log n)\cdot\mathrm{OPT}$" is read as the upper bound, the only direction the proof shows and uses. The hypothesis $c^Tx\ge0$ on $\mathcal X$ is added: the proof uses $d^Ty^*(a)\le\mathrm{OPT}$, which needs $c^Tx^*\ge0$, and Theorem 4.1 is false without it. Indices are 0-based.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 4.1, p. 17

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction

namespace BudgetedAffine.Disjoint

open Matrix

/-- Lemma 4.1: for an optimal solution `(x*, y*)` of (1.1) over the disjoint constrained budgeted
set with value `OPT`, any online covering algorithm for `B̃` with competitive ratio `ρ`, and any
run `a₁, …, a_L` of Algorithm 1, the online cost `ν_L = A(a₁, …, a_L)` is at most `ρ · OPT`. -/
theorem lemma_4_1 {m n L : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : BudgetedAffine.Budget.IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hS : IsPartition S) (hw : ∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : BudgetedAffine.Budget.IsOptimalAR A B c d X (disjointBudgetSet S w) xs ys)
    (OPT : ℝ) (hOPT : BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) = (OPT : EReal))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (alg : OnlineCover (Btil A B xs) d ρ)
    (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m))
    (ha : IsGreedyRun alg w (hatS S A xs) σ a) :
    nu alg a L ≤ ρ * OPT := by sorry

end BudgetedAffine.Disjoint
