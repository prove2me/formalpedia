-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_doubled_hash_AP_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:05:38.949068+00:00
-- url     : https://prove2.me/submissions/4fe30a5d-1496-4f33-8795-c1714ef1a0a9

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_type2_cyclic_data
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {R : Type} [CommRing R] {N L G : ℕ}
    (b : Fin 3 → R) (w : Fin 3 → Fin (2 * N) → R)
    (x y z : CWQ6Type2CyclicEdge N L G)
    (hsupp : CWQ6Type2CyclicCoordinatewiseSupported x y z) :
    let H0 := fun e : CWQ6Type2CyclicEdge N L G ↦
      cwQ6DoubledXHash (b 0) (w 0) (e.1.1 0) +
        4 * cwQ6DoubledZHash (b 1) (w 1) (e.2.1.1 2) -
        2 * cwQ6DoubledYHash (b 2) (w 2) (e.2.2.1 1)
    let H1 := fun e : CWQ6Type2CyclicEdge N L G ↦
      cwQ6DoubledYHash (b 0) (w 0) (e.1.1 1) -
        2 * cwQ6DoubledXHash (b 1) (w 1) (e.2.1.1 0) +
        4 * cwQ6DoubledZHash (b 2) (w 2) (e.2.2.1 2)
    let H2 := fun e : CWQ6Type2CyclicEdge N L G ↦
      cwQ6DoubledZHash (b 0) (w 0) (e.1.1 2) +
        cwQ6DoubledYHash (b 1) (w 1) (e.2.1.1 1) +
        cwQ6DoubledXHash (b 2) (w 2) (e.2.2.1 0)
    H0 x + H1 y = 2 * H2 z := by
  dsimp only
  have ha := mme_CW_q6_doubled_hash_AP_identity
    (b 0) (w 0) x.1.1 y.1.1 z.1.1 hsupp.1
  have hb := mme_CW_q6_doubled_hash_AP_identity
    (b 1) (w 1) y.2.1.1 z.2.1.1 x.2.1.1 hsupp.2.1
  have hc := mme_CW_q6_doubled_hash_AP_identity
    (b 2) (w 2) z.2.2.1 x.2.2.1 y.2.2.1 hsupp.2.2
  linear_combination ha - 2 * hb - 2 * hc
