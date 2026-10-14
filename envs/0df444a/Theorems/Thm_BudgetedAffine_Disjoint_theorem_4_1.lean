-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_theorem_4_1
-- name    : BudgetedAffine.Disjoint.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:48.838987+00:00
-- url     : https://prove2.me/theorems/cd6fc2ab-55b7-4329-a7cc-b40f60e8a68e
-- title:
--   Theorem 4.1 — for disjoint constrained budgeted sets, z_Aff(U) = O(log² n / log log n)·z_AR(U)
-- statement:
--   Consider the two-stage adjustable robust problem (1.1) with $A\in\mathbb R^{m\times n}$, $B\in\mathbb R^{m\times n}_+$, $c,d\in\mathbb R^n_+$, $\mathcal X$ polyhedral with $c^Tx\ge0$ for all $x\in\mathcal X$, and $\mathcal U$ the disjoint constrained budgeted set (4.1) for a partition $S_1,\dots,S_L$ of $[m]$ and weights $w_{\ell i}\in[0,1]$. Then
--   $$z_{Aff}(\mathcal U)=O\Big(\frac{\log^2n}{\log\log n}\Big)\cdot z_{AR}(\mathcal U),$$
--   i.e. there are a constant $C>0$ and a threshold $N$ such that for every $n\ge N$, every $m$, every number of blocks $L$ and every such instance,
--   $$z_{Aff}(\mathcal U)\le C\cdot\frac{\log^2n}{\log\log n}\cdot z_{AR}(\mathcal U).$$
--
--   Here $n$ is the number of decision variables. The bound does not depend on $m$ or on the number $L$ of budget constraints.
--
--   **Formalization Note** $C$ and $N$ are chosen before $m$, $L$ and the instance. Values are extended reals, so an infeasible problem gives $z_{AR}=+\infty$ and the bound holds trivially. $\log$ is the natural logarithm and $\log^2n=(\log n)^2$. The hypothesis $c^Tx\ge0$ on $\mathcal X$ is added: without it the statement is false (with $L=1$, $m=n=1$, $A=0$, $B=c=d=1$, $\mathcal X=\{x\ge-5\}$, $w=1$, one has $z_{AR}=z_{Aff}=-4$, and padding with zero columns makes $C\log^2n/\log\log n>1$). It holds whenever $\mathcal X\subseteq\mathbb R^n_+$. The online covering algorithm used by the proof does not appear in the statement.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Theorem 4.1, p. 15

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model

namespace BudgetedAffine.Disjoint

open Matrix

/-- Theorem 4.1: for disjoint constrained budgeted sets,
`z_Aff(U) = O(log² n / log log n) · z_AR(U)`, with the constant `C` and the threshold `N` uniform
over `m`, the number of blocks `L`, and every instance. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m L : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
      (c d : Fin n → ℝ) (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m))
      (w : Fin L → Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → BudgetedAffine.Budget.IsPolyhedral X →
      (∀ x ∈ X, 0 ≤ c ⬝ᵥ x) → IsPartition S → (∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1) →
      BudgetedAffine.Budget.zAff A B c d X (disjointBudgetSet S w) ≤
        ((C * (Real.log n ^ 2 / Real.log (Real.log n)) : ℝ) : EReal) *
          BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) := by sorry

end BudgetedAffine.Disjoint
