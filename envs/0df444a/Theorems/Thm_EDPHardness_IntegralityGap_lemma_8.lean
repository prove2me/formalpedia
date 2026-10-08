-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_lemma_8
-- name    : EDPHardness.IntegralityGap.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:38.307978+00:00
-- url     : https://prove2.me/theorems/10f4425b-0459-4a2b-a4e9-b32eba7b64a5
-- title:
--   Lemma 8 — Pr[ℰ₃] ≤ 1/4 for every integer g > 2: G′ has at most (6β₂c²)^{g+1} cycles of length ≤ g
-- statement:
--   Let $H$ be the random hypergraph on $n$ vertices with $m=\lfloor\beta_2n\rfloor$ independent hyperedges, each uniform among the $c$-subsets, let $G'$ be the graph on the hyperedges obtained from $G(H)$ by shrinking every special edge, and let $K_g$ be the number of (simple) cycles of length at most $g$ in $G'$. The event $\mathcal E_3$ (for the value $g$) is $K_g>(6\beta_2c^2)^{g+1}$.
--
--   Let $2\le c\le n$ and assume $\beta_2>0$. Then for every integer $g>2$,
--   $$\Pr\big[K_g>(6\beta_2c^2)^{g+1}\big]\le\frac14 .$$
--
--   Short cycles of $G'$ are what a short non-canonical path must create together with a canonical path; the lemma says there are few of them.
--
--   **Formalization Note** The paper's definition says "cycles of length at most $g$ in $G$", but its proof ("a cycle $C$ of length $k$ in the graph $G'$") and its use in Section 2.4 count cycles in $G'$; cycles in $G'$ are formalized. Each cycle is counted once, as its edge set. The proof needs no largeness of $n$; the hypotheses $c\le n$ (the hyperedges exist) and $\beta_2>0$ (otherwise there are no hyperedges and the threshold can be negative) are the ones the statement needs to be the paper's.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), pp. 493–495, Lemma 8 (statement p. 494)

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem lemma_8 (n c : ℕ) (hc : 2 ≤ c) (hcn : c ≤ n) (hβ₂ : 0 < beta2 n c) (g : ℕ) (hg : 2 < g) :
    hypProb n (numEdges n c) c (E3 n c g) ≤ 1 / 4 := by sorry

end EDPHardness.IntegralityGap
