-- Prove2me | Theorems.Thm_BudgetedAffine_NetworkGap_Supplement_theorem_5_1
-- name    : BudgetedAffine.NetworkGap.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:37:52.569511+00:00
-- url     : https://prove2.me/theorems/541238bf-f26f-4c10-80c2-763edb75c88f
-- title:
--   Theorem 5.1 — permutation invariant intersections of L budgets: z_Aff(U) = O(log L · log n / log log n)·z_AR(U) (corrected: L = 1 endpoint)
-- statement:
--   Consider the two-stage adjustable robust problem (1.1):
--   $$z_{AR}(\mathcal U)=\min_{x\in\mathcal X}\ c^\top x+\max_{h\in\mathcal U}\ \min_{y(h)\ge0}\ \big\{d^\top y(h)\ :\ Ax+By(h)\ge h\big\},$$
--   with $A\in\mathbb R^{m\times n}$, a fixed nonnegative recourse matrix $B\in\mathbb R^{m\times n}_+$ and costs $c,d\in\mathbb R^n_+$, and let $z_{Aff}(\mathcal U)$ be the same value when the recourse is restricted to affine policies $y(h)=Ph+q$ (feasible for every $h\in\mathcal U$, including $Ph+q\ge0$). Suppose that
--
--   1. $\mathcal U$ is an intersection of $L$ budget constraints (1.3), $\mathcal U=\{h\in[0,1]^m : \sum_{i\in S_\ell}w_{\ell i}h_i\le1\ \forall\ell\in[L]\}$, with arbitrary $S_\ell\subseteq[m]$ and $w_{\ell i}\in[0,1]$;
--   2. $\mathcal U$ is permutation invariant (Definition 5.1);
--   3. $\mathcal X$ is a polyhedral cone.
--
--   Then there are absolute constants $C>0$ and $N$ such that for every $n\ge N$, every $m$, every $L$ and every such instance,
--   $$z_{Aff}(\mathcal U)\ \le\ C\,\log L\cdot\frac{\log n}{\log\log n}\cdot z_{AR}(\mathcal U)\quad(L\ge2),\qquad z_{Aff}(\mathcal U)\ \le\ C\,\frac{\log n}{\log\log n}\cdot z_{AR}(\mathcal U)\quad(L=1).$$
--
--   The theorem shows that symmetry of the uncertainty set costs only a factor logarithmic in the number of budget constraints, compared with the single-budget guarantee of Theorem 3.1, instead of the linear factor of Theorem 5.2 for arbitrary intersections. It covers the CLT sets (5.1).
--
--   **Formalization Note** The values $z_{AR}$ and $z_{Aff}$ are the published `BudgetedAffine.Budget.zAR`/`zAff`: infima in the extended reals of the worst-case cost $\sup_{h\in\mathcal U}(c^\top x+d^\top y(h))$ over feasible solutions, so an infeasible problem has value $+\infty$ and an unbounded one $-\infty$. The second stage is a policy $h\mapsto y(h)$, which gives the same value as choosing $y(h)$ separately for each $h$. No sign condition on $c^\top x$ over $\mathcal X$ and no restriction $x\ge0$ is imposed, as in the paper. "$O(\cdot)$" is read uniformly: $C$ and $N$ are chosen before $n$, $m$, $L$ and all instance data. Logarithms are natural. Indices are 0-based. The uncertainty set is the published `BudgetedAffine.Disjoint.disjointBudgetSet`; its body has no partition premise, so its use adds no disjointness assumption.
--
--   Differences from the source:
--   - correction: $z_{Aff}=O(\log L\cdot\log n/\log\log n)\cdot z_{AR}$ for every $L$ → for $L=1$ the factor is $C\log n/\log\log n$; reason: at $L=1$, $\log L=0$ and the printed bound would assert $z_{Aff}\le0$, false for $m=1$, any $n$, $\mathcal X=\{0\}$, $A=0$, $B=(1,0,\dots,0)$, $c=0$, $d=(1,0,\dots,0)$, $S_1=\{1\}$, $w=1$, where $z_{AR}=z_{Aff}=1$; a single constraint (1.3) is a budget set (1.2), for which Theorem 3.1 and Theorem 5.2 with $L=1$ give exactly this rate; no case is excluded.
--   - encoding: $z_{Aff}(\mathcal U)=O(f)\cdot z_{AR}(\mathcal U)$ → $\exists C>0,\exists N,\ \forall n\ge N$, uniformly in $m$, $L$ and the instance, $z_{Aff}\le C f\cdot z_{AR}$; reason: the paper's $O(\cdot)$ is in $n$ with absolute constants; a large-$n$ threshold also makes $\log\log n>0$.
--   - encoding: "the intersection of $L$ budget constraints", $\ell\in[L]$ → both clauses are conditional on $L\ge2$ or $L=1$, so $L=0$ carries no claim; reason: (1.3) has at least one constraint; only the case without constraints, outside the source, is left out.
--   - encoding: optimal values as minima → extended-real infima over policies, $+\infty$ if infeasible; reason: Lean convention, the same values on every instance.
--   - encoding: indices $1,\dots,m$ and $\ell\in[L]$ → 0-based `Fin m`, `Fin L`; reason: Lean convention.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Theorem 5.1, p. 21 (proof pp. 22–23); model (1.1), p. 1; (1.3), p. 4; Definition 5.1, p. 21

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_NetworkGap_Supplement_Setting

namespace BudgetedAffine.NetworkGap.Supplement

open Matrix BudgetedAffine.Budget

/-- Theorem 5.1: for a permutation invariant intersection of `L` budget constraints (1.3) and a
polyhedral cone `X`, `z_Aff(U) = O(log L · log n / log log n) · z_AR(U)` for every `L ≥ 2`, and
`z_Aff(U) = O(log n / log log n) · z_AR(U)` at the endpoint `L = 1`, with the constant `C` and the
threshold `N` uniform over `m`, `L` and every instance. -/
theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m L : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
      (c d : Fin n → ℝ) (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m))
      (w : Fin L → Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → IsPolyhedralCone X →
      (∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1) → IsPermInvariant (BudgetedAffine.Disjoint.disjointBudgetSet S w) →
      (2 ≤ L →
        zAff A B c d X (BudgetedAffine.Disjoint.disjointBudgetSet S w) ≤
          ((C * Real.log L * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) *
            zAR A B c d X (BudgetedAffine.Disjoint.disjointBudgetSet S w)) ∧
      (L = 1 →
        zAff A B c d X (BudgetedAffine.Disjoint.disjointBudgetSet S w) ≤
          ((C * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) *
            zAR A B c d X (BudgetedAffine.Disjoint.disjointBudgetSet S w)) := by sorry

end BudgetedAffine.NetworkGap.Supplement
