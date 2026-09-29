-- Prove2me | Theorems.Thm_ChvatalPolytopes_Perfect_isPerfect_iff_integer_minmax
-- name    : ChvatalPolytopes.Perfect.isPerfect_iff_integer_minmax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:15:25.933407+00:00
-- url     : https://prove2.me/theorems/2c30a3ba-bbf0-45f8-b0f8-1b574c8c5a38
-- title:
--   Theorem 3.1, proof — perfection is equivalent to the fractional clique-cover min–max (iii)
-- statement:
--   Let $G=(V,E)$ be a finite graph, $S(G)$ the incidence vectors of its stable sets and $C(G)$ the vertex sets of its maximal cliques. Then $G$ is perfect if and only if the following condition (iii) holds: for every integer-valued vector $c=(c_u:u\in V)$,
--   $$\max\{cx : x\in S(G)\}=\min\Big\{\sum_{W\in C(G)}\lambda_W \;:\; \lambda_W\ge0 \text{ for all } W\in C(G),\ \sum_{W\in C(G),\,u\in W}\lambda_W\ge c_u \text{ for all } u\in V\Big\}.$$
--
--   Condition (iii) is what Proposition 2.1 turns statement (i) of Theorem 3.1 into; this equivalence is therefore the combinatorial heart of Theorem 3.1. It upgrades the defining zero–one min–max for zero–one weights to a fractional min–max for all integer weights.
--
--   **Formalization Note** "max = min" is written out: some $m$ is the maximum of $cx$ over $S(G)$ (`IsStableMax`), some real $\lambda\ge0$ satisfying the covering constraints has $\sum_W\lambda_W=m$, and every such $\lambda$ has $\sum_W\lambda_W\ge m$. The weights are functions `Finset V → ℝ` read only on the maximal cliques $C(G)$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 141, §3, proof of Theorem 3.1, condition (iii) and the equivalence (iii) ⇔ (ii)

import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect

namespace ChvatalPolytopes.Perfect

/-- **Condition (iii) ⇔ (ii)** (Chvátal 1975, §3, proof of Theorem 3.1, p. 141). A graph `G` is
perfect if and only if (iii): for every integer-valued vector `c = (c_u : u ∈ V)`, the maximum of
`{cx : x ∈ S(G)}` is equal to the minimum of
`{Σ (λ_W : W ∈ C(G)) : λ_W ≥ 0 for all W ∈ C(G) and Σ (λ_W : u ∈ W ∈ C(G)) ≥ c_u for all u ∈ V}`.

"max = min" is spelled out: some `m` is the maximum over `S(G)`, is attained by a feasible
nonnegative real `λ`, and is at most the objective of every feasible `λ`. Weights are
`λ : Finset V → ℝ`, read only on `C(G) = maximalCliques G` (maximal cliques). -/
theorem isPerfect_iff_integer_minmax {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    IsPerfect G ↔
      ∀ c : V → ℤ, ∃ m : ℝ, IsStableMax G (fun u => (c u : ℝ)) m ∧
        (∃ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, 0 ≤ lam W) ∧
          (∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) ∧
          ∑ W ∈ maximalCliques G, lam W = m) ∧
        (∀ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, 0 ≤ lam W) →
          (∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) →
          m ≤ ∑ W ∈ maximalCliques G, lam W) := by sorry

end ChvatalPolytopes.Perfect
