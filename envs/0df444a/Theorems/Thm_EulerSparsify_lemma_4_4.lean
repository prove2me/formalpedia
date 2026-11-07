-- Prove2me | Theorems.Thm_EulerSparsify_lemma_4_4
-- name    : EulerSparsify.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:48.848903+00:00
-- url     : https://prove2.me/theorems/68ef907a-48d3-423a-8ca4-77e57b935120
-- title:
--   Lemma 4.4 — $\sum_{i:e\in E_i}b_i\le 2w_e$ and $\sum_{i:e\in E_i}b_i^2\le\frac43w_e^2$
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph with positive weights and let $\{K_i,F_i,b_i\}_{i\in[I]}$ be a $\rho$-nested ER partitioning of $G$ for some $\rho$. Then for every edge $e\in E$,
--
--   $$\sum_{i:\,e\in E_i}b_i\le 2w_e,\qquad\sum_{i:\,e\in E_i}b_i^2\le\frac43\,w_e^2 .\tag{4.1}$$
--
--   An edge is used for routing by at most one subgraph per dyadic weight scale below its own weight, so the total routing load it carries is bounded by its weight. This feeds the norm bound of Lemma 5.3 and the variance bound of Lemma 5.8.
--
--   Differences from the source:
--   - reading: "a nested ER partitioning" → ρ-nested for any ρ; reason: item 2 is not used
--   - encoding: weighted graph of Definition 2.1 → all weights positive; reason: Definition 2.1 uses w_min and b_i = 2^j w_min
--   - reading: Definition 2.1 → IsNestedER: j ∈ ℤ, item 4 vertex-disjoint; reason: the proof uses at most one i ∈ I_j with e ∈ E_i; Σ_{j ≤ k} 2^j = 2^{k+1} over ℤ
--   - generalization: graph → parallel edges and self-loops allowed; reason: the statement involves only the weights and edge sets
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 4.4, eq. (4.1), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_EulerSparsify_IsNestedER

namespace EulerSparsify

/-- **Lemma 4.4** (edge overlap of a nested ER partitioning), equation (4.1), p.14, PDF p.16.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 4.4: "For a nested ER partitioning {K_i, F_i, b_i}_{i∈[I]} of G, the edge weight
satisfies that for any e ∈ E, Σ_{i: e∈E_i} b_i ≤ 2w_e, Σ_{i: e∈E_i} b_i² ≤ (4/3) w_e². (4.1)"

**Formalization Note.** "A nested ER partitioning" with no quality: the statement holds for a
`ρ`-nested ER partitioning with any `ρ` (it does not use item 2). `G` has positive weights
(Definition 2.1 uses `w_min`); parallel edges and self-loops are allowed. -/
theorem lemma_4_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (hw : ∀ e, 0 < G.w e) (ρ : ℝ) (P : NestedFamily V E)
    (hP : IsNestedER G ρ P) (e : E) :
    ∑ i ∈ Finset.univ.filter (fun i => e ∈ P.Ed i), P.b G i ≤ 2 * G.w e ∧
      ∑ i ∈ Finset.univ.filter (fun i => e ∈ P.Ed i), P.b G i ^ 2 ≤ 4 / 3 * G.w e ^ 2 := by sorry

end EulerSparsify
