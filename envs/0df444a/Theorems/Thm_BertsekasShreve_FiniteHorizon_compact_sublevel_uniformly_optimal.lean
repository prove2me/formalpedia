-- Prove2me | Theorems.Thm_BertsekasShreve_FiniteHorizon_compact_sublevel_uniformly_optimal
-- name    : BertsekasShreve.FiniteHorizon.compact_sublevel_uniformly_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:38:32.376197+00:00
-- url     : https://prove2.me/theorems/0c235cee-da04-443d-9954-01f1e3e6ef78
-- title:
--   Proposition 3.4 — compact sublevel sets U_k(x, λ) give J*_N = T^N(J_0) and a uniformly N-stage optimal policy
-- statement:
--   Let $(S,C,U,H)$ be a model satisfying the Monotonicity Assumption, $J_0\in F$ with $J_0(x)>-\infty$ for all $x$, and $N\ge1$. Let the control space $C$ be a Hausdorff topological space, and assume that for each $x\in S$, $\lambda\in R$ and $k=0,1,\dots,N-1$ the set
--   $$U_k(x,\lambda)=\{u\in U(x)\mid H[x,u,T^k(J_0)]\le\lambda\}$$
--   is compact (the empty set counts as compact). Then
--   $$J^*_N=T^N(J_0),$$
--   and there exists a uniformly $N$-stage optimal policy.
--
--   This is the standard compactness route to existence of optimal policies in finite-horizon problems, for instance for deterministic problems with continuous data and coercive costs.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 46, Proposition 3.4, eq. (16) of Chapter 3

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.4 (Bertsekas & Shreve 1996, p. 46). Let the control space `C` be a Hausdorff
space and assume that for each `x ∈ S`, `λ ∈ R` and `k = 0, 1, …, N − 1` the set
`U_k(x, λ) = {u ∈ U(x) | H[x, u, T^k(J₀)] ≤ λ}` (eq. (16) of Chapter 3) is compact. Then
`J*_N = T^N(J₀)` and there exists a uniformly `N`-stage optimal policy. -/
theorem compact_sublevel_uniformly_optimal {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : Model S C) (J₀ : S → EReal) (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N)
    (hcpt : ∀ x (lam : ℝ) (k : ℕ), k < N →
      IsCompact {u | u ∈ m.U x ∧ m.H x u (m.T^[k] J₀) ≤ (lam : EReal)}) :
    m.optCostN J₀ N = m.T^[N] J₀ ∧ ∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π := by sorry

end BertsekasShreve.FiniteHorizon
