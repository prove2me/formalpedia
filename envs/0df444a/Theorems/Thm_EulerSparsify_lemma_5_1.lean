-- Prove2me | Theorems.Thm_EulerSparsify_lemma_5_1
-- name    : EulerSparsify.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:13.183213+00:00
-- url     : https://prove2.me/theorems/297c11f8-db2b-4fed-a2a6-aea3e22e71dd
-- title:
--   Lemma 5.1 — the $Q_i$ are mutually orthogonal projections onto circulations with $[Q_i]_{ff}\ge1-\rho$
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph with positive weights and let $\{K_i,F_i,b_i\}_{i\in[I]}$ be a $\rho$-nested ER partitioning of $G$, with $Q_i=P_{C(E_i)}-P_{C(E_i\setminus F_i)}$. Then
--
--   1. each $Q_i$ is an orthogonal projection: $Q_i^\top=Q_i$ and $Q_i^2=Q_i$;
--   2. $\mathrm{im}(Q_i)\subseteq C(E_i)$;
--   3. the projections are orthogonal to each other: $Q_iQ_j=0$ for $i\neq j$;
--   4. for every $f\in F_i$, $[Q_i]_{ff}\ge 1-\rho$.
--
--   The $Q_i$ can therefore be composed into the single routing matrix $R$ of (5.1), and each owned edge keeps a constant share of its own demand.
--
--   Differences from the source:
--   - encoding: "Q_i is an orthogonal projection" → Q_iᵀ = Q_i and Q_i² = Q_i; reason: the definition of an orthogonal projection matrix
--   - encoding: weighted graph G of Definition 2.1 → all weights positive; reason: Definition 2.1 uses w_min and b_i = 2^j w_min, (5.1) uses W⁻¹, and §5 applies these lemmas to (V, supp(w), w_supp(w)); a zero weight only makes W⁻¹ undefined
--   - reading: Definition 2.1 → IsNestedER: j ∈ ℤ, item 4 vertex-disjoint, diam_ER(K̂_i) ≤ ρ including connectivity of K̂_i on U_i; reason: the proof of Proposition 4.3 says the K_i of a bucket are vertex disjoint and that K̂_i is connected as diam_ER ≤ ρ; ER across components is +∞
--   - generalization: graph (2-sparse incidence rows) → parallel edges and self-loops allowed; reason: a self-loop has a zero row of B, so 1_e is a circulation by itself and contributes nothing to L, R b_f or the variance terms; parallel edges arise in und(G⃗) and are part of the paper's graphs
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 5.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_EulerSparsify_IsNestedER
import Definitions.Def_EulerSparsify_Qmat

namespace EulerSparsify

/-- **Lemma 5.1**, p.16, PDF p.18.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 5.1: "Let {K_i, F_i, b_i}_{i∈[I]} be a ρ-nested ER partition of G. Then, each Q_i is an
orthogonal projection with im(Q_i) ⊆ C(E_i) and the projections are orthogonal to each other,
i.e., for each i ≠ j ∈ [I], Q_iQ_j = 0. Moreover, for all f ∈ F_i, it satisfies that
[Q_i]_ff ≥ 1 − ρ."

Four clauses: each `Q_i` is symmetric and idempotent; its image lies in `C(E_i)`; `Q_iQ_j = 0` for
`i ≠ j`; `[Q_i]_ff ≥ 1 − ρ` for `f ∈ F_i`.

**Formalization Note.** `G` has positive weights (Definition 2.1); parallel edges and self-loops
are allowed. An orthogonal projection matrix is a symmetric idempotent matrix. -/
theorem lemma_5_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (hw : ∀ e, 0 < G.w e) (ρ : ℝ) (P : NestedFamily V E)
    (hP : IsNestedER G ρ P) :
    (∀ i, (Qmat G P i).transpose = Qmat G P i ∧ Qmat G P i * Qmat G P i = Qmat G P i) ∧
    (∀ i (x : EuclideanSpace ℝ E), Matrix.toEuclideanLin (Qmat G P i) x ∈ G.circ (P.Ed i)) ∧
    (∀ i i', i ≠ i' → Qmat G P i * Qmat G P i' = 0) ∧
    (∀ i, ∀ f ∈ P.F i, 1 - ρ ≤ Qmat G P i f f) := by sorry

end EulerSparsify
