-- Prove2me | Theorems.Thm_DirectedSearch_Approx_lemma_4_7
-- name    : DirectedSearch.Approx.lemma_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:05.827305+00:00
-- url     : https://prove2.me/theorems/62a51a50-fbd2-47f8-987b-e0d3d2ba8447
-- title:
--   Lemma 4.7, p. 23 — an edge-weighted forest keeps half its weight on vertex-disjoint stars
-- statement:
--   Let $G$ be a forest on a finite vertex set and $\mathrm{wt}$ a real weight on its edges. There is a subgraph $H\le G$ that is a union of vertex-disjoint star graphs (every edge of $H$ has an endpoint of degree 1 in $H$) with
--   $$\sum_{e\in E(G)}\mathrm{wt}(e)\le 2\sum_{e\in E(H)}\mathrm{wt}(e).$$
--
--   This is Step (2) of the approximation: each star of $H$ becomes a star-shaped submarket.
--
--   **Formalization Note.** The paper's "at least half that of the original tree" is read as the original forest, the lemma's hypothesis. No sign condition is placed on the weights.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 23, Lemma 4.7 (citing Banerjee et al. 2017)

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Graphs

namespace DirectedSearch.Approx
theorem lemma_4_7 {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (wt : Sym2 V → ℝ) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsStarForest H ∧ graphWeight G wt ≤ 2 * graphWeight H wt := by sorry
end DirectedSearch.Approx
