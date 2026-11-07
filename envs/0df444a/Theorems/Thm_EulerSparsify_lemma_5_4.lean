-- Prove2me | Theorems.Thm_EulerSparsify_lemma_5_4
-- name    : EulerSparsify.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:25.777196+00:00
-- url     : https://prove2.me/theorems/75439672-06ec-4c7e-ac13-7edadd59751c
-- title:
--   Lemma 5.4 — a circulation subspace $S$ with $\dim S\ge m/32$ and $P_S\preceq256RR^\top$
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph with positive weights, $n=|V|$, $m=|E|$, and let $\{K_i,F_i,b_i\}_{i\in[I]}$ be a $\rho$-nested ER partitioning of $G$ with $\rho\le\tfrac12$ and $m\ge 64n$. Then there is a linear subspace $S\subseteq\mathbb R^E$ such that
--
--   $$\dim(S)\ge\frac m{32},\qquad S\subseteq\ker(B^\top W),\qquad P_S\preceq 256\cdot RR^\top .$$
--
--   Every $x\in S$ gives a degree-preserving update $w\circ x=Wx$, and the partial colouring of Algorithm 5.1 is carried out in $S$.
--
--   Differences from the source:
--   - encoding: S ⊂ ker(BᵀW) → Bᵀ(Wx) = 0 for every x ∈ S; reason: the definition of the kernel
--   - encoding: weighted graph G of Definition 2.1 → all weights positive; reason: Definition 2.1 uses w_min and b_i = 2^j w_min, (5.1) uses W⁻¹, and §5 applies these lemmas to (V, supp(w), w_supp(w)); a zero weight only makes W⁻¹ undefined
--   - reading: Definition 2.1 → IsNestedER: j ∈ ℤ, item 4 vertex-disjoint, diam_ER(K̂_i) ≤ ρ including connectivity of K̂_i on U_i; reason: the proof of Proposition 4.3 says the K_i of a bucket are vertex disjoint and that K̂_i is connected as diam_ER ≤ ρ; ER across components is +∞
--   - generalization: graph (2-sparse incidence rows) → parallel edges and self-loops allowed; reason: a self-loop has a zero row of B, so 1_e is a circulation by itself and contributes nothing to L, R b_f or the variance terms; parallel edges arise in und(G⃗) and are part of the paper's graphs
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 5.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_EulerSparsify_IsNestedER
import Definitions.Def_EulerSparsify_routingMat
import Definitions.Def_EulerSparsify_DiGraph_lap

namespace EulerSparsify

/-- **Lemma 5.4**, p.17, PDF p.19.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 5.4: "Given a ρ-nested ER partitioning of G, where ρ ≤ 1/2 and m ≥ 64n, there is a
subspace S ⊂ ℝ^E such that dim(S) ≥ m/32, S ⊂ ker(BᵀW), P_S ≼ 256 · RRᵀ".

**Formalization Note.** `n = |V|`, `m = |E|`; `G` has positive weights (Definition 2.1, `W⁻¹` in
`R`); parallel edges and self-loops are allowed. `S` is a subspace of `EuclideanSpace ℝ E`;
`S ⊂ ker(BᵀW)` is `Bᵀ(Wx) = 0` for `x ∈ S`; `P_S = projMat S`; `X ≼ Y` is `(Y − X).PosSemidef`. -/
theorem lemma_5_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (hw : ∀ e, 0 < G.w e) (ρ : ℝ) (hρ : ρ ≤ 1 / 2)
    (hm : 64 * Fintype.card V ≤ Fintype.card E) (P : NestedFamily V E)
    (hP : IsNestedER G ρ P) :
    ∃ S : Submodule ℝ (EuclideanSpace ℝ E),
      (Fintype.card E : ℝ) / 32 ≤ (Module.finrank ℝ S : ℝ) ∧
      (∀ x ∈ S, G.incMat.transpose.mulVec (G.wMat.mulVec (fun e => x e)) = 0) ∧
      ((256 : ℝ) • (routingMat G P * (routingMat G P).transpose) - projMat S).PosSemidef := by sorry

end EulerSparsify
