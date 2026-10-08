-- Prove2me | Theorems.Thm_BertsekasShreve_Generalized_prop6_3a_uniform_optimal_iff_attained
-- name    : BertsekasShreve.Generalized.prop6_3a_uniform_optimal_iff_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:55:29.822987+00:00
-- url     : https://prove2.me/theorems/e34c021f-57f3-405a-8b77-f103b092ea1e
-- title:
--   Proposition 6.3(a) — a uniformly $N$-stage optimal policy exists iff the DP infima are attained
-- statement:
--   Consider the generalized abstract model of Section 6.1 under conditions A.1–A.4 and the exact selection assumption, and let $N$ be a positive integer. There exists a uniformly $N$-stage optimal policy in $\tilde\Pi$ if and only if the infimum in
--   $$T^{k+1}(J_0)(x)=\inf_{u\in U(x)}H[x,u,T^k(J_0)]$$
--   is attained (by some $u\in U(x)$) for each $x\in S$ and $k=0,1,\dots,N-1$.
--
--   The exact selection assumption is what allows pointwise minimizers to be assembled into a selector in the restricted class $\tilde M$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 96, Proposition 6.3(a)

import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model
import Definitions.Def_BertsekasShreve_Generalized_Assumptions
import Definitions.Def_BertsekasShreve_Generalized_Optimality

namespace BertsekasShreve.Generalized

open Filter Topology

/-- Proposition 6.3(a), p. 96. Under A.1–A.4 and the exact selection assumption, a uniformly
`N`-stage optimal policy exists if and only if the infimum in
`T^{k+1}(J₀)(x) = inf_{u ∈ U(x)} H[x, u, T^k(J₀)]` is attained for each `x ∈ S` and
`k = 0, 1, …, N − 1`. `N` is a positive integer (p. 28). -/
theorem prop6_3a_uniform_optimal_iff_attained {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hES : P.ExactSelection)
    (N : ℕ) (hN : 0 < N) :
    (∃ π : P.Policy, P.IsUniformlyNStageOptimal N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ P.U x, P.H x u (P.T^[k] P.J0) = P.T^[k + 1] P.J0 x := by sorry

end BertsekasShreve.Generalized
