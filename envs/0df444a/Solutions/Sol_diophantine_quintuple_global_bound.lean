-- Prove2me | solution 1 for diophantine_quintuple_global_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T19:52:45.866981+00:00
-- url     : https://prove2.me/submissions/ed6648b8-fb29-4d33-8db0-b3cc9db9f828
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_diophantine_quintuple_ac_bound
import Theorems.Thm_diophantine_quintuple_d_bound
import Definitions.Def_diophantine_descent

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open DiophantineDescent

theorem _root_.solution (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) :
    f 0 * f 2 < 67700000000000000000000000 ∧
      f 3 < 18300000000000000000000000000000000000000000000000000 :=
  ⟨diophantine_quintuple_ac_bound f hq ho, diophantine_quintuple_d_bound f hq ho⟩

#print axioms solution
