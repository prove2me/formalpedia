-- Prove2me | Theorems.Thm_EulerSparsify_lemma_5_8
-- name    : EulerSparsify.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:36.572561+00:00
-- url     : https://prove2.me/theorems/b1b2f10d-fb37-4d43-813d-bd86d135dce0
-- title:
--   Lemma 5.8 — matrix variance of the routing matrix is at most $2\rho\,\Pi_V$
-- statement:
--   Let $\vec G=(V,E,w)$ have positive weights, let $G=\mathrm{und}(\vec G)$, and let $\{K_i,F_i,b_i\}_{i\in[I]}$ be a $\rho$-nested ER partitioning of $G$ with $\rho>0$ and routing matrix $R$ (5.1). For $e\in E$ define
--
--   $$\tilde A_e=L_G^{\dagger/2}\Bigl(\sum_{f\in E}[R]_{fe}\,w_f\,b_f\,e_{h(f)}^\top\Bigr)L_G^{\dagger/2},$$
--
--   where $b_f$ is the row of $B$ indexed by $f$ and $e_{h(f)}$ the indicator of the head (source) of $f$. Then, with $\Pi_V=I-\frac1{|V|}\mathbf 1\mathbf 1^\top$,
--
--   $$\sum_{e\in E}\tilde A_e\tilde A_e^\top\preceq 2\rho\,\Pi_V,\qquad\sum_{e\in E}\tilde A_e^\top\tilde A_e\preceq 2\rho\,\Pi_V .$$
--
--   The variance $O(\rho)=O(n/m)$ is what the matrix partial colouring converts into an $O(\sqrt{n/m})$ spectral error.
--
--   **Formalization Note** No connectivity of $G$ is assumed.
--
--   Differences from the source:
--   - encoding: G⃗ and G = und(G⃗) → one DiGraph: same edges and weights; L_G = BᵀWB; reason: und(G⃗) keeps the edges and weights (p.10)
--   - encoding: weighted graph G of Definition 2.1 → all weights positive; reason: Definition 2.1 uses w_min and b_i = 2^j w_min, (5.1) uses W⁻¹, and §5 applies these lemmas to (V, supp(w), w_supp(w)); a zero weight only makes W⁻¹ undefined
--   - reading: Definition 2.1 → IsNestedER: j ∈ ℤ, item 4 vertex-disjoint, diam_ER(K̂_i) ≤ ρ including connectivity of K̂_i on U_i; reason: the proof of Proposition 4.3 says the K_i of a bucket are vertex disjoint and that K̂_i is connected as diam_ER ≤ ρ; ER across components is +∞
--   - generalization: graph (2-sparse incidence rows) → parallel edges and self-loops allowed; reason: a self-loop has a zero row of B, so 1_e is a circulation by itself and contributes nothing to L, R b_f or the variance terms; parallel edges arise in und(G⃗) and are part of the paper's graphs
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 5.8, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_EulerSparsify_IsNestedER
import Definitions.Def_EulerSparsify_routingMat
import Definitions.Def_EulerSparsify_DiGraph_lap
import Definitions.Def_EulerSparsify_sqrtPinv

namespace EulerSparsify

/-- **Lemma 5.8** (matrix variance of the routing matrix), p.19, PDF p.21.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 5.8: "For ⃗G = (V, E, w), let {K_i, F_i, b_i}_{i∈[I]} be a ρ-nested ER partitioning of
G := und(⃗G) for ρ > 0. Let R be the corresponding routing matrix defined in Equation (5.1). Define
for all e ∈ E Ã_e := L_G^{†/2} (Σ_{f∈E} [R]_fe w_f b_f eᵀ_{h(f)}) L_G^{†/2}. Then,
Σ_{e∈E} Ã_e Ã_eᵀ ≼ 2ρ · Π_V, Σ_{e∈E} Ã_eᵀ Ã_e ≼ 2ρ · Π_V."

**Formalization Note.** `⃗G` and `G = und(⃗G)` are the same `DiGraph` (same edges and weights); the
weights are positive (Definition 2.1, `W⁻¹` in `R`); parallel edges and self-loops are allowed.
`b_f` is row `f` of `B` (as a vector on `V`), `e_{h(f)}` the indicator of the head (source) of
`f`, `L_G^{†/2} = sqrtPinv G.lap`, `Π_V = I − (1/|V|)𝟙𝟙ᵀ` (p.10) and `X ≼ Y` is
`(Y − X).PosSemidef`. No connectivity of `G` is assumed. -/
theorem lemma_5_8 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (hw : ∀ e, 0 < G.w e) (ρ : ℝ) (hρ : 0 < ρ) (P : NestedFamily V E)
    (hP : IsNestedER G ρ P) :
    let X := sqrtPinv G.lap
    let A : E → Matrix V V ℝ := fun e =>
      X * (∑ f, (routingMat G P f e * G.w f) •
        Matrix.vecMulVec (fun v => G.incMat f v) (Pi.single (G.head f) 1)) * X
    let PiV : Matrix V V ℝ :=
      1 - (Fintype.card V : ℝ)⁻¹ • Matrix.of (fun (_ _ : V) => (1 : ℝ))
    ((2 * ρ) • PiV - ∑ e, A e * (A e).transpose).PosSemidef ∧
      ((2 * ρ) • PiV - ∑ e, (A e).transpose * A e).PosSemidef := by sorry

end EulerSparsify
