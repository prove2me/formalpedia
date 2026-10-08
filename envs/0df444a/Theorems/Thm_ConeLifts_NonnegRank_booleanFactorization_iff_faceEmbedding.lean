-- Prove2me | Theorems.Thm_ConeLifts_NonnegRank_booleanFactorization_iff_faceEmbedding
-- name    : ConeLifts.NonnegRank.booleanFactorization_iff_faceEmbedding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:13:02.461464+00:00
-- url     : https://prove2.me/theorems/b03e2be1-a349-4689-8dce-b48b3f0b9f64
-- title:
--   Theorem 4.11 — Boolean factorizations of $\operatorname{supp}(S_C)$ and embeddings of $L(C)$ into $2^{[k]}$
-- statement:
--   Let $C \subseteq \mathbb{R}^n$ be a polytope with the origin in its interior, let $L(C)$ be its face lattice (all faces, including $\emptyset$ and $C$, ordered by inclusion), and let $k \in \mathbb{N}$. Then
--
--   $$\operatorname{supp}(S_C) \text{ has a Boolean factorization of intermediate dimension } k \iff L(C) \text{ embeds into the Boolean lattice } 2^{[k]} .$$
--
--   Here $2^{[k]}$ is the set of subsets of $[k] = \{1, \dots, k\}$ ordered by inclusion, and an embedding is a map $\varphi : L(C) \to 2^{[k]}$ with $H \subseteq F \iff \varphi(H) \subseteq \varphi(F)$ for all faces $H, F$.
--
--   The theorem translates the Boolean rank of the slack matrix, a purely combinatorial quantity of the vertex–facet incidences, into an order-theoretic property of the face lattice, so that lower bounds on the nonnegative rank can be read off from the facial structure of the polytope.
--
--   **Formalization Note** The paper says "lattice embedding"; both directions of its proof use and produce exactly an order embedding (inclusion-preserving and inclusion-reflecting), and the map $\varphi(F) = \bigcup_{v \in F} A(v)$ constructed there need not preserve joins or meets. The Lean statement therefore uses an order embedding `Face C ↪o Finset (Fin k)`. Faces are exposed faces; the columns of $S_C$ are indexed by $\operatorname{ext}(C^\circ)$, the facet of a column $y$ being $\{x \in C : \langle x, y\rangle = 1\}$.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 15, Theorem 4.11

import Mathlib
import Definitions.Def_ConeLifts_NonnegRank_IsPolytope
import Definitions.Def_ConeLifts_NonnegRank_Face
import Definitions.Def_ConeLifts_NonnegRank_HasBooleanFactorization

namespace ConeLifts.NonnegRank

/-- **Theorem 4.11** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 15). For a polytope `C`
(with the origin in its interior), there is a Boolean factorization of `supp(S_C)` of intermediate
dimension `k` if and only if there is a lattice embedding of the face lattice `L(C)` into the
Boolean lattice `2^[k]` (`Finset (Fin k)` ordered by inclusion).

Reading decision: "lattice embedding" is an order embedding (`H ⊆ F ↔ φ H ⊆ φ F`), which is exactly
what both directions of the paper's proof use and produce; the map `φ(F) = ⋃_{v ∈ F} A(v)` built in
the proof need not preserve joins or meets. -/
theorem booleanFactorization_iff_faceEmbedding {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) (k : ℕ) :
    HasBooleanFactorization C k ↔ Nonempty (Face C ↪o Finset (Fin k)) := by sorry

end ConeLifts.NonnegRank
