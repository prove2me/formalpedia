-- Prove2me | Theorems.Thm_BunkbedAux_wzEdges_support
-- name    : BunkbedAux.wzEdges_support
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T04:14:02.969097+00:00
-- url     : https://prove2.me/theorems/255a0aca-0d28-49d3-a522-d3d7cbaae284
-- title:
--   The canonical edge set of a state touches only its three lifted vertices
-- statement:
--   The canonical edge set that a Wierman--Ziff state $s$ contributes for a hyperedge $(a,b,c)$ on level $l$ consists of edges among the three lifted vertices $(a,l)$, $(b,l)$, $(c,l)$ only. This theorem records that: every endpoint of every such edge is one of those three.
--
--   The statement is immediate by inspection of the five states, but it is worth having as a lemma rather than re-deriving, because it is exactly the *support* hypothesis needed to apply the boundary-partition principle.
--
--   **Mathematical role.** To conclude that connectivity in a union of parts depends only on the partitions the parts induce on a boundary set, one needs that no vertex outside the boundary is shared between parts. In the Wierman--Ziff bunkbed graph the parts are the per-hyperedge, per-level canonical edge sets together with the posts, and the boundary is the set of lifted hypergraph vertices. This lemma says each such part is supported on its own three lifted vertices, all of which lie in the boundary — so the support hypothesis holds trivially, with no non-boundary vertices at all. That is what allows a gadget copy, whose configuration does involve many private internal vertices, to be exchanged for the abstract state it simulates.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Sections 3.2 and 4 (pp. 3, 6-7).

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **The canonical edge set of a state touches only its own three lifted vertices.** -/
theorem wzEdges_support {V : Type*} [DecidableEq V] (a b c : V) (l : Fin 2) (s : WZ)
    (e : Sym2 (V × Fin 2)) (he : e ∈ WZ.edges s (a, b, c) l) (v : V × Fin 2) (hv : v ∈ e) :
    v = (a, l) ∨ v = (b, l) ∨ v = (c, l) := by
  sorry

end BunkbedAux
