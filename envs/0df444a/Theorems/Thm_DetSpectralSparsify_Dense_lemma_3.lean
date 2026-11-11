-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_3
-- name    : DetSpectralSparsify.Dense.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:12.816068+00:00
-- url     : https://prove2.me/theorems/c7225224-0bcf-48f6-b634-f145cbb7ceb9
-- title:
--   Lemma 3 (Edge-disjoint composition) — unions of sparsifiers of edge-disjoint pieces
-- statement:
--   Suppose $G=G_1\,\dot\cup\,\cdots\,\dot\cup\,G_t$ is an edge-disjoint union of multigraphs on the same vertex set and $H_i$ is a $(1\pm\varepsilon)$-spectral sparsifier of $G_i$ for every $i\in[t]$. Then
--   $$H:=H_1\,\dot\cup\,\cdots\,\dot\cup\,H_t$$
--   is a $(1\pm\varepsilon)$-spectral sparsifier of $G$.
--
--   The lemma combines the sparsifiers of clusters, dyadic weight classes and block pairs into one global sparsifier.
--
--   **Formalization Note** $G$ and $H$ are the canonical edge-disjoint unions `Multigraph.union`, whose edges are indexed by the disjoint union of the edge sets of the pieces.
--
--   Differences from the source:
--   - encoding: G = G₁ ∪̇ ⋯ ∪̇ G_t, an edge-disjoint decomposition → G is the canonical union graph `union Gs`; reason: any edge-disjoint decomposition is this union up to relabelling the edges, which does not change L_G
--   - generalization: weighted graphs → arbitrary real edge weights and any real ε; reason: the statement only uses additivity of Laplacians; positive weights and ε ∈ (0,1) are special cases
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.5, Lemma 3

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 3 (Edge-disjoint composition), p.5. If `H_i` is a `(1 ± ε)`-spectral sparsifier of
`G_i` for every `i`, then the edge-disjoint union of the `H_i` is a `(1 ± ε)`-spectral
sparsifier of the edge-disjoint union of the `G_i`. -/
theorem lemma_3 {n t : ℕ} (ε : ℝ) (Gs Hs : Fin t → Multigraph n)
    (h : ∀ i, IsSpectralSparsifier ε (Gs i) (Hs i)) :
    IsSpectralSparsifier ε (Multigraph.union Gs) (Multigraph.union Hs) := by sorry

end DetSpectralSparsify.Dense
