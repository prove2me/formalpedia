-- Prove2me | Theorems.Thm_BertsekasShreve_FiniteHorizon_exists_uniformly_optimal_iff_attained
-- name    : BertsekasShreve.FiniteHorizon.exists_uniformly_optimal_iff_attained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:36:52.596382+00:00
-- url     : https://prove2.me/theorems/eaf1cb41-0f1f-4d76-a762-b069576e26c0
-- title:
--   Corollary 3.3.1 — a uniformly N-stage optimal policy exists iff the DP infima are attained; then J*_N = T^N(J_0)
-- statement:
--   Let $(S,C,U,H)$ be a model satisfying the Monotonicity Assumption, $J_0\in F$ with $J_0(x)>-\infty$ for all $x$, and $N\ge1$.
--
--   1. There exists a uniformly $N$-stage optimal policy if and only if the infimum in
--   $$T^{k+1}(J_0)(x)=\inf_{u\in U(x)}H[x,u,T^k(J_0)]$$
--   is attained for each $x\in S$ and $k=0,1,\dots,N-1$, i.e. there is $u\in U(x)$ with $H[x,u,T^k(J_0)]=T^{k+1}(J_0)(x)$.
--   2. If there exists a uniformly $N$-stage optimal policy, then $J^*_N=T^N(J_0)$.
--
--   Attainment of the minimum in the DP recursion is therefore exactly what is needed to build a uniformly optimal policy, and it already forces the DP algorithm to give the optimal cost.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 45, Corollary 3.3.1, eq. (15) of Chapter 3

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Corollary 3.3.1 (Bertsekas & Shreve 1996, p. 45).
(a) A uniformly `N`-stage optimal policy exists if and only if the infimum in
`T^{k+1}(J₀)(x) = inf_{u ∈ U(x)} H[x, u, T^k(J₀)]` (eq. (15) of Chapter 3) is attained for each
`x ∈ S` and `k = 0, 1, …, N − 1`.
(b) If a uniformly `N`-stage optimal policy exists, then `J*_N = T^N(J₀)`. -/
theorem exists_uniformly_optimal_iff_attained {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) :
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ m.U x, m.H x u (m.T^[k] J₀) = m.T^[k + 1] J₀ x) ∧
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) →
      m.optCostN J₀ N = m.T^[N] J₀) := by sorry

end BertsekasShreve.FiniteHorizon
