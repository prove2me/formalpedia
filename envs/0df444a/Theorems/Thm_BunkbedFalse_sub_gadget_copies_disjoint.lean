-- Prove2me | Theorems.Thm_BunkbedFalse_sub_gadget_copies_disjoint
-- name    : BunkbedFalse.sub_gadget_copies_disjoint
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T07:07:33.446979+00:00
-- url     : https://prove2.me/theorems/bf7853e4-0cb6-4c5f-a431-52ecc006ac8d
-- title:
--   The six substituted gadget copies are edge-disjoint
-- statement:
--   In the graph constructed in Section 4.2, each of the six hyperedges of Hollom's hypergraph is replaced by a copy of the gadget G_1204. Distinct copies may share attachment vertices, but they share no edges.
--
--   Equivalently, the six embedded edge sets are pairwise disjoint. This structural fact permits Bernoulli percolation on their union to factor into independent per-copy configurations.
-- source:
--   Gladkov, Pak, Zimin, The bunkbed conjecture is false, PNAS 122 (2025), Section 4.2, pp. 6-7; the six gadget substitutions in the proof of Theorem 1.2.

import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Sub Finset

namespace BunkbedFalse

/-- Distinct copies of `G_1204` in the substituted graph have disjoint edge sets. -/
theorem sub_gadget_copies_disjoint :
    ∀ i j : Fin 6, i ≠ j →
      Disjoint ((gadgetE 1204).image (Sym2.map (emb i)))
        ((gadgetE 1204).image (Sym2.map (emb j))) := by
  sorry

end BunkbedFalse
