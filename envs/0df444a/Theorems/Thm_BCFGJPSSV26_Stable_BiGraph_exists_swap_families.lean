-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_BiGraph_exists_swap_families
-- name    : BCFGJPSSV26.Stable.BiGraph.exists_swap_families
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:47:31.339466+00:00
-- url     : https://prove2.me/theorems/fe7a8aac-ae65-472d-a51d-67c12780c612
-- title:
--   Lemma 6.2 (Part II) — swap families on star-like bipartite graphs
-- statement:
--   This is a variant of Lemma 6.2 of Part II: a star-like bipartite graph has families of small swaps that cover it and that, on average, use every left vertex of degree at most $1$ at most $1+8/N$ times.
--
--   Let $G$ be a bipartite graph with finite sets $L$ (left) and $R$ (right) of vertices; the degree of a vertex is its number of neighbours on the other side. Assume that $G$ is *star-like*: every edge has an endpoint of degree at most $1$. Assume $|R|\le|L|$, and let $N\ge 200$ be an integer. A *swap* is a pair $\sigma=(L_\sigma,R_\sigma)$ of finite sets. Call a finite list $\mathcal S$ of swaps *good* if
--
--   1. $L_\sigma\subseteq L$ and $R_\sigma\subseteq R$ for every $\sigma$ in $\mathcal S$;
--   2. $|R_\sigma|\le|L_\sigma|\le 24N$ for every $\sigma$ in $\mathcal S$;
--   3. for every $\sigma$ in $\mathcal S$, every neighbour in $R$ of a vertex of $L_\sigma$ is in $R_\sigma$;
--   4. every $v\in R$ is in $R_\sigma$ for some $\sigma$ in $\mathcal S$;
--   5. every $u\in L$ of degree less than $2N$ is in $L_\sigma$ for some $\sigma$ in $\mathcal S$;
--   6. every $u\in L$ of degree at least $2$ is in $L_\sigma$ for at most one entry $\sigma$ of $\mathcal S$;
--   7. every $v\in R$ of degree at most $1$ is in $R_\sigma$ for at most one entry $\sigma$ of $\mathcal S$;
--   8. $\mathcal S$ has at most $|L|+2$ entries.
--
--   Then there are an integer $b\ge 1$ and good lists $\mathcal S_1,\dots,\mathcal S_b$ such that every $u\in L$ of degree at most $1$ satisfies
--
--   $$\sum_{r=1}^{b}\#\{\sigma\in\mathcal S_r:\ u\in L_\sigma\}\;\le\;\Bigl(1+\frac{8}{N}\Bigr)\,b,$$
--
--   where entries of a list are counted with multiplicity.
--
--   The lemma is the combinatorial core of the refined local-search bound (Theorem 3.6). There $L$ and $R$ are the clusters of the local-search solution inside $D_0$ and the clusters of the benchmark, joined when they intersect; cross-freeness makes this graph star-like. Every swap of a family is tested against approximate local optimality, and the inequalities are summed over a family and averaged over the families.
--
--   **Formalization Note** The statement differs from the paper's Lemma 6.2 in allowing isolated vertices and $|R|<|L|$. Vertices are elements of two arbitrary types with decidable equality, and degrees count only neighbours inside $L$ and $R$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Lemma 6.2 (a variant). Lean source: `BCFGJPSSV26.Stable.BiGraph.exists_swap_families`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/StarForest.lean#L815-L824

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForestAux
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForest

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace BiGraph

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (G : BiGraph α β)

end BiGraph

namespace BiGraph

open StarForestAux

variable {α β : Type*}

variable {G : BiGraph α β}

end BiGraph

namespace BiGraph

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (G : BiGraph α β)

theorem exists_swap_families {N : ℕ} (hN : 200 ≤ N) (hG : G.IsStarLike)
    (hc : G.R.card ≤ G.L.card) :
    ∃ (b : ℕ) (_ : 0 < b) (𝒮 : Fin b → List (Swap α β)), (∀ r, G.Good N (𝒮 r)) ∧
      ∀ u ∈ G.L, G.degL u ≤ 1 →
        (∑ r, ((𝒮 r).countP fun σ ↦ u ∈ σ.Ls : ℝ)) ≤ (1 + 8 / N) * b := by sorry

end BiGraph
end BCFGJPSSV26.Stable
end
