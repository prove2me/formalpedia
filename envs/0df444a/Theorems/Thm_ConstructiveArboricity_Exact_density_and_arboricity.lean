-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_density_and_arboricity
-- name    : ConstructiveArboricity.Exact.density_and_arboricity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:26.929008+00:00
-- url     : https://prove2.me/theorems/78d026ef-3285-4686-8833-a2d16e3a0611
-- title:
--   Lemma 2.1 — Density and arboricity
-- statement:
--   For every finite simple undirected graph $G$, with pseudoarboricity $\rho(G)$ and arboricity $a(G)$,
--
--   $$\rho(G)\le a(G)\le\rho(G)+1.$$
--
--   Both quantities are defined from the graph, with no assumed partition or optimal orientation as input. They are zero for an edgeless graph. This places the exact minimum forest count among two consecutive integers once pseudoarboricity is known.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph with its edge sets → vertices Fin n, edge identities Fin m, an injective unordered endpoint map, and color fibers; reason: every finite simple graph admits such labels; isolated vertices and empty color classes are retained
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1476.pdf, Lemma 2.1, p.7; proof p.8

import Mathlib
import Definitions.Def_ConstructiveArboricity_Exact_Graph

namespace ConstructiveArboricity.Exact

/-- Gholami et al., STOC 2027 submission #1476 (October 2026), Lemma 2.1,
p.7; proof p.8. PDF sha256
9aa896d448cf63b4f502235eca19f59eb0468fad89783d21467b281518e3c512. -/
theorem density_and_arboricity (G : Graph) :
    G.rho ≤ G.arboricity ∧ G.arboricity ≤ G.rho + 1 := by sorry

end ConstructiveArboricity.Exact
