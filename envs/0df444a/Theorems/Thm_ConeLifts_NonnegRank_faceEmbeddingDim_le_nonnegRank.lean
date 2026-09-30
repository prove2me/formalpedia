-- Prove2me | Theorems.Thm_ConeLifts_NonnegRank_faceEmbeddingDim_le_nonnegRank
-- name    : ConeLifts.NonnegRank.faceEmbeddingDim_le_nonnegRank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:13:42.967981+00:00
-- url     : https://prove2.me/theorems/cf0720a9-6625-421a-943f-aafa03706578
-- title:
--   Corollary 4.12 — $\operatorname{rank}_+(C)$ is at least the least $k$ with $L(C) \hookrightarrow 2^{[k]}$
-- statement:
--   Let $C \subseteq \mathbb{R}^n$ be a polytope with the origin in its interior, and let $k_0$ be the smallest integer $k$ such that the face lattice $L(C)$ embeds into the Boolean lattice $2^{[k]}$. Then
--
--   $$\operatorname{rank}_+(C) \ \ge\ k_0 .$$
--
--   This lower bound on the nonnegative rank depends only on the face lattice of $C$, not on its metric realization; it is the common source of the antichain and face-count bounds of Corollary 4.13.
--
--   **Formalization Note** "Embedding" is an order embedding, as in Theorem 4.11. $k_0$ is written as `sInf` of the set of $k$ admitting an embedding; that set is nonempty for a polytope (it has finitely many faces, and $F \mapsto \{\text{faces contained in } F\}$ embeds $L(C)$ into the subsets of the set of faces), so the `sInf` is its minimum. $\operatorname{rank}_+(C)$ is valued in `ℕ∞`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 15, Corollary 4.12

import Mathlib
import Definitions.Def_ConeLifts_NonnegRank_IsPolytope
import Definitions.Def_ConeLifts_NonnegRank_Face
import Definitions.Def_ConeLifts_NonnegRank_nonnegRank

namespace ConeLifts.NonnegRank

/-- **Corollary 4.12** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 15). Let `C ⊆ ℝⁿ` be a
polytope (with the origin in its interior) and `k` the smallest integer such that there is an
embedding of the face lattice `L(C)` into the Boolean lattice `2^[k]`. Then `rank₊(C) ≥ k`.

The set of such `k` is nonempty for a polytope (a polytope has finitely many faces, and
`F ↦ {faces contained in F}` embeds `L(C)` into `2^[#L(C)]`), so the `sInf` is its minimum.
"Embedding" is an order embedding, as in Theorem 4.11. `rank₊(C)` is valued in `ℕ∞`. -/
theorem faceEmbeddingDim_le_nonnegRank {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) :
    ((sInf {k : ℕ | Nonempty (Face C ↪o Finset (Fin k))} : ℕ) : ℕ∞) ≤ nonnegRank C := by sorry

end ConeLifts.NonnegRank
