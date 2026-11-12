-- Prove2me | Theorems.Thm_BunkbedAux_reach_image_map
-- name    : BunkbedAux.reach_image_map
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T04:57:45.676277+00:00
-- url     : https://prove2.me/theorems/2fe14d4d-881c-4b23-946a-11da0e4fc040
-- title:
--   Reachability transports along an injective relabelling
-- statement:
--   Relabelling the vertices of a graph by an injective map should not change which pairs of vertices are connected. This theorem is that statement for the edge-set presentation used here: for injective $f$ and any finite set $S$ of edges,
--
--   $$f(u) \leftrightarrow f(v) \ \text{ in } \ \mathrm{ofEdges}\bigl(\mathrm{Sym}^2(f)[S]\bigr) \iff u \leftrightarrow v \ \text{ in } \ \mathrm{ofEdges}(S).$$
--
--   The implication from right to left is the easy one: $\mathrm{Sym}^2(f)$ carries each edge of $S$ to an edge of the image, so $f$ is a graph homomorphism and homomorphisms preserve reachability.
--
--   The converse needs injectivity, and a little care: a walk in the image graph must be pulled back. Every edge of the image has both endpoints in the range of $f$, so a walk starting at $f(u)$ never leaves the range, and applying a left inverse of $f$ to it yields a walk in the original graph. Without injectivity the statement is false — a non-injective relabelling can merge two vertices and create connections that were not there.
--
--   **Mathematical role.** This is what allows a *copy* of a gadget, embedded in a larger graph, to be analysed as the gadget itself. In the counterexample graph of Theorem 1.2 each of the six gadget copies is an injective image of $G_{1204}$ under a vertex map that sends the gadget's apex and path ends to the corresponding hyperedge vertices and its interior into a private block. This theorem says the copy's connectivity behaviour is that of the gadget, and hence — the weight function at $P = 1/2$ being constant, so that weights transport trivially — that the copy's five partition probabilities are the gadget's.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 4 (pp. 6-7), gadget substitution.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset SimpleGraph

namespace BunkbedAux

/-- **Reachability transports along an injective relabelling.** Relabelling the vertices by an
injective map carries the percolation configuration to its image and preserves connectivity. -/
theorem reach_image_map {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (S : Finset (Sym2 V)) (u v : V) :
    (ofEdges (S.image (Sym2.map f))).Reachable (f u) (f v) ↔ (ofEdges S).Reachable u v := by
  sorry

end BunkbedAux
