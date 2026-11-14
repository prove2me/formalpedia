-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_contractOn_expectation_le
-- name    : ConsistentSubmodular.Objective.contractOn_expectation_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:33.590538+00:00
-- url     : https://prove2.me/theorems/fbbf53ba-b45f-40bb-9f09-7929724a8bb8
-- title:
--   Expected residual after contracting any buffer is at most twice the old optimum
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $[n]$, let $U,B\subseteq[n]$, $k\in\mathbb N$ with $k>0$, and $V\ge0$. Assume $f(A)\le V$ for every $A\subseteq U$ with $|A|\le k$. Let $p\in[0,1]^n$ with $\sum_e p_e\le k$. Then, with the contraction $f_{U,B}(S)=f\big(B\cup(S\cap U)\big)-f(B)$,
--
--   $$\mathbb E_{S\sim p}\big[f_{U,B}(S)\big]\;\le\;2V,$$
--
--   where $S$ contains each element $e$ independently with probability $p_e$.
--
--   Contracting any buffer, even a large one, leaves an expected residual of at most twice the old cardinality-constrained optimum $V$. This supplies the mean bound $M=2V$ in the lower-tail estimate.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SamplingScale.lean#L96-L116 (`ConsistentSubmodular.Objective.contractOn_expectation_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.contractOn_expectation_le (U B : Finset (Fin n)) (k : ℕ) (hk : 0 < k)
    {V : ℝ} (hV : 0 ≤ V)
    (hscale : ∀ A ⊆ U, A.card ≤ k → f.value A ≤ V)
    (p : Fin n → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (hmass : ∑ e, p e ≤ k) :
    finiteExpectation p (f.contractOn U B).value ≤ 2 * V := by sorry
