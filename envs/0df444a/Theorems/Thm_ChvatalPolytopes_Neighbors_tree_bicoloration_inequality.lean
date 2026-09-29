-- Prove2me | Theorems.Thm_ChvatalPolytopes_Neighbors_tree_bicoloration_inequality
-- name    : ChvatalPolytopes.Neighbors.tree_bicoloration_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:21:43.429982+00:00
-- url     : https://prove2.me/theorems/bb0df2f3-0704-47aa-bd02-67c9ecb890d9
-- title:
--   Lemma 6.1 — a tree's two colour classes are the only maximizers of a nonnegative integer weighting
-- statement:
--   Let $T=(V,E)$ be a tree with a bicoloration $V=B\cup R$, and let $S(T)$ be the set of incidence vectors of the stable sets of $T$. Then there are nonnegative integers $c_u$ ($u\in V$) and $m$ such that
--   $$\sum_{u\in V}c_ux_u\le m\qquad\text{for all } x=(x_u:u\in V)\in S(T),$$
--   with equality if and only if $x$ is the incidence vector of $B$ or the incidence vector of $R$:
--   $$x_u=\begin{cases}1 & u\in B\\ 0 & u\in R\end{cases}\qquad\text{or}\qquad x_u=\begin{cases}1 & u\in R\\ 0 & u\in B.\end{cases}$$
--
--   The lemma supplies, for a spanning tree of the symmetric difference of two stable sets, the weights that make exactly those two stable sets optimal; it is the key step of the "if" part of Theorem 6.2.
--
--   **Formalization Note** The tree is Mathlib's `SimpleGraph.IsTree` on a finite type, which includes connectedness and hence a nonempty vertex set. The integers $c_u$ and $m$ are natural numbers, cast to $\mathbb R$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 149, Lemma 6.1

import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_IsBicoloration

namespace ChvatalPolytopes.Neighbors

/-- **Lemma 6.1** (Chvátal 1975, p. 149). Let `T = (V, E)` be a tree with a bicoloration
`V = B ∪ R`. Then there are nonnegative integers `c_u` (`u ∈ V`) and `m` such that
`Σ (c_u x_u : u ∈ V) ≤ m` for all `(x_u : u ∈ V) ∈ S(T)`, with equality if and only if `x` is
the incidence vector of `B` or the incidence vector of `R`. -/
theorem tree_bicoloration_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (B R : Finset V) (hBR : IsBicoloration T B R) :
    ∃ (c : V → ℕ) (m : ℕ), ∀ x ∈ stableVectors T,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) ↔ x = incidenceVector B ∨ x = incidenceVector R) := by sorry

end ChvatalPolytopes.Neighbors
