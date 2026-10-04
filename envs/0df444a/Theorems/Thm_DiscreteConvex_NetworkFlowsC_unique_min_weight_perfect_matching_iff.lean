-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsC_unique_min_weight_perfect_matching_iff
-- name    : DiscreteConvex.NetworkFlowsC.unique_min_weight_perfect_matching_iff
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:48.729837+00:00
-- url     : https://prove2.me/theorems/7fbdc7e3-3f9d-440d-8fbd-393943433ebf
-- title:
--   Proposition 9.24 -- unique_min_weight_perfect_matching_iff
-- statement:
--   **Proposition 9.24** (p.266). A bipartite weighted graph $(V^+,V^-;c)$ with $|V^+|=|V^-|=m$ has a unique minimum-weight perfect matching if and only if there is a potential $\hat p$ and orderings $V^+=\{u_1,\ldots,u_m\}$, $V^-=\{v_1,\ldots,v_m\}$ such that $c(u_i,v_j)+\hat p(u_i)-\hat p(v_j)$ is $0$ when $i=j$, $\ge0$ when $j<i$, and $>0$ when $i<j$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, Proposition 9.24.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, Proposition 9.24

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsMinWeightMatching
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MinWeightValue

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Proposition 9.24 (p.266). A bipartite weighted graph has a unique minimum-weight perfect
matching iff there is a potential and orderings of the two vertex classes satisfying the
displayed sign pattern (Eq. (9.77)). The minimum weight must be finite: the book's condition is
about matchings of the graph, and a single matching of weight `+∞` would otherwise be a unique
minimum while the right side needs `+∞ + p̂(u) - p̂(v) = 0`. -/
theorem unique_min_weight_perfect_matching_iff (Vp Vn : Finset V) (m : ℕ) (hVp : Vp.card = m)
    (hVn : Vn.card = m) (c : V → V → WithTop ℝ) :
    ((∃! M, IsMinWeightMatching Vp Vn c M) ∧ MinWeightValue Vp Vn c ≠ ⊤) ↔
    ∃ (phat : V → ℝ) (ordU ordV : Fin m → V), (∀ i, ordU i ∈ Vp) ∧ (∀ i, ordV i ∈ Vn) ∧
      Function.Injective ordU ∧ Function.Injective ordV ∧
      ∀ i j : Fin m,
        (i = j → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) = 0) ∧
        ((j:ℕ) < (i:ℕ) → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) ≥ 0) ∧
        ((i:ℕ) < (j:ℕ) → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) > 0) := by sorry

end DiscreteConvex.NetworkFlowsC
