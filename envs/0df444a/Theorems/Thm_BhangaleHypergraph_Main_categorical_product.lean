-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_categorical_product
-- name    : BhangaleHypergraph.Main.categorical_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:06:01.823632+00:00
-- url     : https://prove2.me/theorems/222ded8b-97bc-4aa3-895e-9675a04b2931
-- title:
--   Lemma 2.10 — Categorical product coloring
-- statement:
--   For every simple graph $G$ on an arbitrary vertex type and every natural $C$, the categorical product has adjacency in both coordinates and obeys
--   $$\chi(G)>C\Longrightarrow\chi(G\times K_{C+1})>C.$$
--   No finiteness hypothesis is imposed on $G$.
--
--   This is the complete product-coloring implication used for avoiding-set amplification.
--
--   Differences from the source:
--   - encoding: χ(G)>C for arbitrary graphs → absence of a proper Fin C coloring; reason: non-C-colorability expresses the same inequality and also covers infinite chromatic number
--   - encoding: the categorical product with K_{C+1} → adjacency in G together with distinct Fin (C+1) coordinates; reason: this is exactly the source product, with a zero-based complete-graph coordinate
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 2.10, p. 9 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Restricted

namespace BhangaleHypergraph.Main

theorem categorical_product {V : Type} (G : SimpleGraph V) (C : ℕ)
    (hG : ¬ G.Colorable C) : ¬ (ProductComplete G C).Colorable C := by sorry

end BhangaleHypergraph.Main
