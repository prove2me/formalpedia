-- Prove2me | Theorems.Thm_EulerSparsify_lemma_5_9
-- name    : EulerSparsify.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:27.385176+00:00
-- url     : https://prove2.me/theorems/c73e417a-8357-438a-9ef2-edfee022552a
-- title:
--   Lemma 5.9 — matrix variance on the subspace $S$ is at most $512\rho\,\Pi_V$
-- statement:
--   Let $\vec G=(V,E,w)$ have positive weights, $G=\mathrm{und}(\vec G)$, and let $\{K_i,F_i,b_i\}_{i\in[I]}$ be a $\rho$-nested ER partitioning of $G$ with $\rho>0$ and routing matrix $R$. Let $S\subseteq\mathbb R^E$ satisfy the conditions of Lemma 5.4,
--
--   $$\dim(S)\ge\frac m{32},\qquad S\subseteq\ker(B^\top W),\qquad P_S\preceq256\,RR^\top,$$
--
--   and for $e\in E$ define $\tilde A_e=L_G^{\dagger/2}\bigl(\sum_{f\in E}[P_S]_{fe}\,w_f\,b_f\,e_{h(f)}^\top\bigr)L_G^{\dagger/2}$. Then
--
--   $$\sum_{e\in E}\tilde A_e\tilde A_e^\top\preceq512\rho\,\Pi_V,\qquad\sum_{e\in E}\tilde A_e^\top\tilde A_e\preceq512\rho\,\Pi_V .$$
--
--   This is the variance bound that Proposition 3.9 needs inside Algorithm 5.1.
--
--   Differences from the source:
--   - reading: "S satisfies the conditions in Lemma 5.4" → the three displayed properties of S: dim(S) ≥ m/32, S ⊂ ker(BᵀW), P_S ≼ 256 RRᵀ; reason: these are the conditions Lemma 5.4 states for S; its hypotheses ρ ≤ 1/2, m ≥ 64n concern the existence of S
--   - encoding: G⃗ and G = und(G⃗) → one DiGraph: same edges and weights; L_G = BᵀWB; reason: und(G⃗) keeps the edges and weights (p.10)
--   - encoding: weighted graph G of Definition 2.1 → all weights positive; reason: Definition 2.1 uses w_min and b_i = 2^j w_min, (5.1) uses W⁻¹, and §5 applies these lemmas to (V, supp(w), w_supp(w)); a zero weight only makes W⁻¹ undefined
--   - reading: Definition 2.1 → IsNestedER: j ∈ ℤ, item 4 vertex-disjoint, diam_ER(K̂_i) ≤ ρ including connectivity of K̂_i on U_i; reason: the proof of Proposition 4.3 says the K_i of a bucket are vertex disjoint and that K̂_i is connected as diam_ER ≤ ρ; ER across components is +∞
--   - generalization: graph (2-sparse incidence rows) → parallel edges and self-loops allowed; reason: a self-loop has a zero row of B, so 1_e is a circulation by itself and contributes nothing to L, R b_f or the variance terms; parallel edges arise in und(G⃗) and are part of the paper's graphs
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 5.9, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_EulerSparsify_IsNestedER
import Definitions.Def_EulerSparsify_routingMat
import Definitions.Def_EulerSparsify_DiGraph_lap
import Definitions.Def_EulerSparsify_sqrtPinv

namespace EulerSparsify

/-- **Lemma 5.9** (matrix variance on the subspace `S`), p.21, PDF p.23.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 5.9: "For ⃗G = (V, E, w), let {K_i, F_i, b_i}_{i∈[I]} be a ρ-nested ER partitioning of
G := und(⃗G) for ρ > 0. Let S be a subspace that satisfies the conditions in Lemma 5.4 and P_S be
its orthogonal projection. Define for all e ∈ E Ã_e := L_G^{†/2} (Σ_{f∈E} [P_S]_fe w_f b_f
eᵀ_{h(f)}) L_G^{†/2}. Then, Σ_{e∈E} Ã_e Ã_eᵀ ≼ 512ρ · Π_V, Σ_{e∈E} Ã_eᵀ Ã_e ≼ 512ρ · Π_V."

**Formalization Note.** "The conditions in Lemma 5.4" are its three properties of `S`:
`dim(S) ≥ m/32`, `S ⊂ ker(BᵀW)`, `P_S ≼ 256 RRᵀ`. Conventions as in Lemma 5.8: one `DiGraph` for
`⃗G` and `und(⃗G)`, positive weights, parallel edges and self-loops allowed,
`Π_V = I − (1/|V|)𝟙𝟙ᵀ`, `P_S = projMat S`. -/
theorem lemma_5_9 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (hw : ∀ e, 0 < G.w e) (ρ : ℝ) (hρ : 0 < ρ) (P : NestedFamily V E)
    (hP : IsNestedER G ρ P) (S : Submodule ℝ (EuclideanSpace ℝ E))
    (hdim : (Fintype.card E : ℝ) / 32 ≤ (Module.finrank ℝ S : ℝ))
    (hker : ∀ x ∈ S, G.incMat.transpose.mulVec (G.wMat.mulVec (fun e => x e)) = 0)
    (hPS : ((256 : ℝ) • (routingMat G P * (routingMat G P).transpose) - projMat S).PosSemidef) :
    let X := sqrtPinv G.lap
    let A : E → Matrix V V ℝ := fun e =>
      X * (∑ f, (projMat S f e * G.w f) •
        Matrix.vecMulVec (fun v => G.incMat f v) (Pi.single (G.head f) 1)) * X
    let PiV : Matrix V V ℝ :=
      1 - (Fintype.card V : ℝ)⁻¹ • Matrix.of (fun (_ _ : V) => (1 : ℝ))
    ((512 * ρ) • PiV - ∑ e, A e * (A e).transpose).PosSemidef ∧
      ((512 * ρ) • PiV - ∑ e, (A e).transpose * A e).PosSemidef := by sorry

end EulerSparsify
