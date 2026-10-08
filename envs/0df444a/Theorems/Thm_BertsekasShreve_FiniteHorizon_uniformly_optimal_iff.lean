-- Prove2me | Theorems.Thm_BertsekasShreve_FiniteHorizon_uniformly_optimal_iff
-- name    : BertsekasShreve.FiniteHorizon.uniformly_optimal_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:36:13.062509+00:00
-- url     : https://prove2.me/theorems/469501cd-e821-4087-8653-b3a05eb9b820
-- title:
--   Proposition 3.3 — π* is uniformly N-stage optimal iff T_{μ_k*}T^{N−k−1}(J_0) = T^{N−k}(J_0) for all k < N
-- statement:
--   Let $(S,C,U,H)$ be a model satisfying only the Monotonicity Assumption, let $J_0\in F$ with $J_0(x)>-\infty$ for all $x\in S$, and let $N\ge1$. A policy $\pi^*=(\mu^*_0,\mu^*_1,\dots)$ is uniformly $N$-stage optimal if and only if
--   $$(T_{\mu^*_k}T^{N-k-1})(J_0)=T^{N-k}(J_0),\qquad k=0,\dots,N-1.$$
--
--   In words: a policy is uniformly optimal exactly when, at each stage, its decision rule attains the minimum in the corresponding step of the dynamic programming algorithm. No continuity or compactness is needed.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 44, Proposition 3.3, eq. (14) of Chapter 3

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.3 (Bertsekas & Shreve 1996, p. 44). Under the Monotonicity Assumption only,
a policy `π* = (μ₀*, μ₁*, …)` is uniformly `N`-stage optimal if and only if
`(T_{μ_k*} T^{N−k−1})(J₀) = T^{N−k}(J₀)` for `k = 0, …, N − 1` (eq. (14) of Chapter 3). -/
theorem uniformly_optimal_iff {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) (π : m.Policy) :
    m.IsUniformlyNStageOptimal J₀ N π ↔
      ∀ k, k < N → m.Tmu (π k) (m.T^[N - k - 1] J₀) = m.T^[N - k] J₀ := by sorry

end BertsekasShreve.FiniteHorizon
