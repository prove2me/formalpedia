-- Prove2me | Theorems.Thm_BunkbedFalse_sub_probability_transfer
-- name    : BunkbedFalse.sub_probability_transfer
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T06:51:39.639667+00:00
-- url     : https://prove2.me/theorems/4dace61e-ea97-4cab-90d1-689e0f7562da
-- title:
--   Boundary-law transfer for the substituted gadget graph
-- statement:
--   Replace each of the six hyperedges of the Hollom hypergraph by the graph gadget G_1204, identifying its three boundary vertices with the ordered hyperedge vertices. Define a five-state Wierman-Ziff law whose state probabilities are exactly the five boundary-partition probabilities of one gadget under Bernoulli percolation at p = 1/2. Then, for any two original hypergraph vertices and either bunkbed level, the connection probability in the substituted graph equals the corresponding connection probability in the Wierman-Ziff hypergraph model. This is the probability-transfer step used in Section 4.2 to pass from Lemma 3.2 and Lemma 4.1 to Theorem 1.2.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025), Section 4.2, pp. 6-7, especially the substitution argument immediately after Lemma 4.1.

import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Hyper Bunkbed.Sub

/-- Exact boundary-law transfer for the six substituted gadgets (GPZ, Section 4.2). -/
theorem BunkbedFalse.sub_probability_transfer (P : WZ → ℚ)
    (habc : P .abc = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hab : P .ab_c = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hac : P .ac_b = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hbc : P .a_bc = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hsep : P .a_b_c = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (x y : Fin 10) (l : Fin 2) :
    bbProb subEdges (fun _ => (1/2 : ℚ)) subT (iota x, 0) (iota y, l) =
      wzProb hollomTriple hollomT P (x, 0) (y, l) := by sorry
