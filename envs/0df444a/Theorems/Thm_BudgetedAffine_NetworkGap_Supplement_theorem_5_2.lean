-- Prove2me | Theorems.Thm_BudgetedAffine_NetworkGap_Supplement_theorem_5_2
-- name    : BudgetedAffine.NetworkGap.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:38:47.195983+00:00
-- url     : https://prove2.me/theorems/0fad176b-a170-4932-a294-b48d53f14346
-- title:
--   Theorem 5.2 — arbitrary intersections of L budgets: z_Aff(U) = O(L · log n / log log n)·z_AR(U)
-- statement:
--   Consider the two-stage adjustable robust problem (1.1):
--   $$z_{AR}(\mathcal U)=\min_{x\in\mathcal X}\ c^\top x+\max_{h\in\mathcal U}\ \min_{y(h)\ge0}\ \big\{d^\top y(h)\ :\ Ax+By(h)\ge h\big\},$$
--   with $A\in\mathbb R^{m\times n}$, a fixed nonnegative recourse matrix $B\in\mathbb R^{m\times n}_+$ and costs $c,d\in\mathbb R^n_+$, and let $z_{Aff}(\mathcal U)$ be the same value when the recourse is restricted to affine policies $y(h)=Ph+q$ (feasible for every $h\in\mathcal U$, including $Ph+q\ge0$). Suppose that $\mathcal X$ is a polyhedral cone and that $\mathcal U$ is an intersection of $L\ge1$ budget constraints (1.3),
--   $$\mathcal U=\Big\{h\in[0,1]^m\ \Big|\ \sum_{i\in S_\ell}w_{\ell i}h_i\le1\quad\forall\ell\in[L]\Big\},$$
--   with arbitrary, possibly overlapping, index sets $S_\ell\subseteq[m]$ and weights $w_{\ell i}\in[0,1]$. Then there are absolute constants $C>0$ and $N$ such that for every $n\ge N$, every $m$, every $L\ge1$ and every such instance,
--   $$z_{Aff}(\mathcal U)\ \le\ C\,L\cdot\frac{\log n}{\log\log n}\cdot z_{AR}(\mathcal U).$$
--
--   Without any structure on the budgets, affine policies thus lose at most a factor linear in the number of constraints relative to the single-budget guarantee of Theorem 3.1; Theorem 5.1 improves the factor to $\log L$ for permutation invariant sets.
--
--   **Formalization Note** The values $z_{AR}$ and $z_{Aff}$ are the published `BudgetedAffine.Budget.zAR`/`zAff`: infima in the extended reals of the worst-case cost $\sup_{h\in\mathcal U}(c^\top x+d^\top y(h))$ over feasible solutions, so an infeasible problem has value $+\infty$ and an unbounded one $-\infty$. The second stage is a policy $h\mapsto y(h)$, which gives the same value as choosing $y(h)$ separately for each $h$. No disjointness of the $S_\ell$, no positivity of the weights, no sign condition on $c^\top x$ over $\mathcal X$ and no restriction $x\ge0$ is imposed, as in the paper. "$O(\cdot)$" is read uniformly: $C$ and $N$ are chosen before $n$, $m$, $L$ and all instance data. Logarithms are natural. Indices are 0-based. The uncertainty set is the published `BudgetedAffine.Disjoint.disjointBudgetSet`; its body has no partition premise, so its use adds no disjointness assumption.
--
--   Differences from the source:
--   - encoding: $z_{Aff}(\mathcal U)=O(L\cdot\log n/\log\log n)\cdot z_{AR}(\mathcal U)$ → $\exists C>0,\exists N,\ \forall n\ge N$, uniformly in $m$, $L$ and the instance, $z_{Aff}\le C L\,(\log n/\log\log n)\, z_{AR}$; reason: the paper's $O(\cdot)$ is in $n$ with absolute constants and keeps the factor $L$ explicit; a large-$n$ threshold also makes $\log\log n>0$.
--   - encoding: "the intersection of $L$ budgeted sets", $\ell\in[L]$ → the hypothesis $1\le L$; reason: (1.3) has at least one constraint, and the proof's average $\bar w=\frac1L\sum_\ell w_\ell$ is undefined at $L=0$; only that undefined case is excluded.
--   - encoding: optimal values as minima → extended-real infima over policies, $+\infty$ if infeasible; reason: Lean convention, the same values on every instance.
--   - encoding: indices $1,\dots,m$ and $\ell\in[L]$ → 0-based `Fin m`, `Fin L`; reason: Lean convention.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Theorem 5.2, p. 24 (proof p. 24); model (1.1), p. 1; (1.3), p. 4

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_NetworkGap_Supplement_Setting

namespace BudgetedAffine.NetworkGap.Supplement

open Matrix BudgetedAffine.Budget

/-- Theorem 5.2: for an arbitrary intersection of `L` budget constraints (1.3) and a polyhedral
cone `X`, `z_Aff(U) = O(L · log n / log log n) · z_AR(U)`, with the constant `C` and the threshold
`N` uniform over `m`, `L` and every instance. -/
theorem theorem_5_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m L : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
      (c d : Fin n → ℝ) (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m))
      (w : Fin L → Fin m → ℝ),
      1 ≤ L → (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → IsPolyhedralCone X →
      (∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1) →
      zAff A B c d X (BudgetedAffine.Disjoint.disjointBudgetSet S w) ≤
        ((C * (L : ℝ) * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) *
          zAR A B c d X (BudgetedAffine.Disjoint.disjointBudgetSet S w) := by sorry

end BudgetedAffine.NetworkGap.Supplement
