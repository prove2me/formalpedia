-- Prove2me | Theorems.Thm_BunkbedFalse_sub_probability_grouping
-- name    : BunkbedFalse.sub_probability_grouping
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T07:07:32.749633+00:00
-- url     : https://prove2.me/theorems/a6bfde9e-efba-4ee3-a87f-0edb760aa61f
-- title:
--   Regroup substituted-graph percolation by boundary states
-- statement:
--   Assume the six embedded copies of G_1204 in the substituted graph have pairwise disjoint edge sets. Give each copy the five-state boundary law obtained from its three attachment vertices under Bernoulli percolation with p = 1/2.
--
--   For every pair of original Hollom vertices x and y and either target level l, the bunkbed connection probability in the substituted graph equals the connection probability in the Wierman-Ziff hypergraph model with that five-state law.
--
--   This is the finite law-of-total-probability step in the proof of Theorem 1.2: configurations are grouped by the boundary partition induced independently by each gadget copy on each level.
-- source:
--   Gladkov, Pak, Zimin, The bunkbed conjecture is false, PNAS 122 (2025), Section 4.2, pp. 6-7, substitution argument in the proof of Theorem 1.2.

import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Hyper Bunkbed.Sub Finset

namespace BunkbedFalse

/-- Regroup the independent configurations of the six disjoint gadget copies by their five
boundary-connectivity states. -/
theorem sub_probability_grouping
    (hdisj : ∀ i j : Fin 6, i ≠ j →
      Disjoint ((gadgetE 1204).image (Sym2.map (emb i)))
        ((gadgetE 1204).image (Sym2.map (emb j))))
    (P : WZ → ℚ)
    (habc : P .abc = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hab : P .ab_c = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hac : P .ac_b = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hbc : P .a_bc = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hsep : P .a_b_c = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (x y : Fin 10) (l : Fin 2) :
    bbProb subEdges (fun _ => (1/2 : ℚ)) subT (iota x, 0) (iota y, l) =
      wzProb hollomTriple hollomT P (x, 0) (y, l) := by
  sorry

end BunkbedFalse
