-- Prove2me | Theorems.Thm_EulerSparsify_lemma_5_3
-- name    : EulerSparsify.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:33.950872+00:00
-- url     : https://prove2.me/theorems/1d6555da-e0c2-4234-be28-8d27749bafc8
-- title:
--   Lemma 5.3 — $RR^\top=W^{-1}(\sum_ib_i^2Q_i)W^{-1}\preceq\frac43I$ and $\operatorname{tr}(R)\ge m/8$
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph with positive weights and $m=|E|$, let $\rho\le\tfrac12$, and let $R$ be the routing matrix (5.1) of a $\rho$-nested ER partitioning $\{K_i,F_i,b_i\}_{i\in[I]}$ of $G$. Then
--
--   $$RR^\top=W^{-1}\Bigl(\sum_{i\in[I]}b_i^2Q_i\Bigr)W^{-1}\preceq\frac43\,I,\qquad \operatorname{tr}(R)\ge\frac m8 .\tag{5.2}$$
--
--   Bounded norm and large trace force $R$ to have $\Omega(m)$ singular values of constant size (Lemma 5.4).
--
--   **Formalization Note** $X\preceq Y$ is "$Y-X$ is positive semidefinite".
--
--   Differences from the source:
--   - encoding: weighted graph G of Definition 2.1 → all weights positive; reason: Definition 2.1 uses w_min and b_i = 2^j w_min, (5.1) uses W⁻¹, and §5 applies these lemmas to (V, supp(w), w_supp(w)); a zero weight only makes W⁻¹ undefined
--   - reading: Definition 2.1 → IsNestedER: j ∈ ℤ, item 4 vertex-disjoint, diam_ER(K̂_i) ≤ ρ including connectivity of K̂_i on U_i; reason: the proof of Proposition 4.3 says the K_i of a bucket are vertex disjoint and that K̂_i is connected as diam_ER ≤ ρ; ER across components is +∞
--   - generalization: graph (2-sparse incidence rows) → parallel edges and self-loops allowed; reason: a self-loop has a zero row of B, so 1_e is a circulation by itself and contributes nothing to L, R b_f or the variance terms; parallel edges arise in und(G⃗) and are part of the paper's graphs
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 5.3, eq. (5.2), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_EulerSparsify_IsNestedER
import Definitions.Def_EulerSparsify_routingMat

namespace EulerSparsify

/-- **Lemma 5.3**, equation (5.2), p.17, PDF p.19.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 5.3: "For ρ ≤ 1/2, the matrix R of a ρ-nested ER partitioning satisfies
RRᵀ = W⁻¹(Σ_{i∈[I]} b_i² Q_i)W⁻¹ ≼ (4/3) I, tr(R) ≥ m/8. (5.2)"

Three clauses: the identity, the Loewner bound and the trace bound, with `m = |E|`.

**Formalization Note.** `G` has positive weights (`W⁻¹`, Definition 2.1); parallel edges and
self-loops are allowed. `R = routingMat G P`, `W⁻¹ = diag(1/w_e)`. The only hypothesis on `ρ` is
`ρ ≤ 1/2`. -/
theorem lemma_5_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (hw : ∀ e, 0 < G.w e) (ρ : ℝ) (hρ : ρ ≤ 1 / 2) (P : NestedFamily V E)
    (hP : IsNestedER G ρ P) :
    routingMat G P * (routingMat G P).transpose =
        Matrix.diagonal (fun e => (G.w e)⁻¹) * (∑ i, P.b G i ^ 2 • Qmat G P i) *
          Matrix.diagonal (fun e => (G.w e)⁻¹) ∧
      ((4 / 3 : ℝ) • (1 : Matrix E E ℝ) - routingMat G P * (routingMat G P).transpose).PosSemidef ∧
      (Fintype.card E : ℝ) / 8 ≤ (routingMat G P).trace := by sorry

end EulerSparsify
