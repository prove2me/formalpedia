-- Prove2me | solution 1 for diophantine_quintuple_fujita_regular
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T19:55:42.678144+00:00
-- url     : https://prove2.me/submissions/a7f21dc3-f722-492c-ac1a-a47b0d567a91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_diophantine_quintuple_fujita_d_formula
import Definitions.Def_diophantine_descent

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open DiophantineDescent

theorem _root_.solution (f : Fin 5 → Nat) (hq : Quintuple f) (ho : Ordered f) :
    ∃ r s t : Nat, f 0 * f 1 + 1 = r ^ 2 ∧ f 0 * f 2 + 1 = s ^ 2 ∧
      f 1 * f 2 + 1 = t ^ 2 ∧
      f 3 = f 0 + f 1 + f 2 + 2 * f 0 * f 1 * f 2 + 2 * r * s * t := by
  obtain ⟨r, hr⟩ := hq.2.2 0 1 (by decide)
  obtain ⟨s, hs⟩ := hq.2.2 0 2 (by decide)
  obtain ⟨t, ht⟩ := hq.2.2 1 2 (by decide)
  exact ⟨r, s, t, hr, hs, ht,
    diophantine_quintuple_fujita_d_formula f hq ho r s t hr hs ht⟩

#print axioms solution
